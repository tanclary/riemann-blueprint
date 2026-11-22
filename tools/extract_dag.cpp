#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

template <typename T, size_t PAGE_BITS = 23>  // 8M elements per page
struct PagedVec {
  static constexpr size_t PAGE_SIZE = size_t(1) << PAGE_BITS;
  static constexpr size_t PAGE_MASK = PAGE_SIZE - 1;
  std::vector<T*> pages;
  size_t sz = 0;

  ~PagedVec() {
    for (T* p : pages) delete[] p;
  }

  void ensure(size_t idx) {
    while ((idx >> PAGE_BITS) >= pages.size()) {
      T* p = new T[PAGE_SIZE]();
      pages.push_back(p);
    }
    if (idx + 1 > sz) sz = idx + 1;
  }

  T& operator[](size_t idx) { return pages[idx >> PAGE_BITS][idx & PAGE_MASK]; }
  const T& operator[](size_t idx) const { return pages[idx >> PAGE_BITS][idx & PAGE_MASK]; }
  size_t size() const { return sz; }
};

enum ExprKind : uint8_t {
  EK_NONE = 0,
  EK_LEAF = 1,    // sort, bvar, lit (a = subtag, b = bvar/lit hash)
  EK_UNARY = 2,   // mdata (a = child ie)
  EK_BINARY = 3,  // app(0), lam(1), forallE(2) (sub = tag, a = e0, b = e1)
  EK_LET = 4,     // letE (a = type, b = val, c = body)
  EK_CONST = 5,   // const (a = name_id)
  EK_PROJ = 6     // proj (a = struct_ie, b = typeName_id, c = idx)
};

#pragma pack(push, 1)
struct ExprNode {
  uint8_t kind;
  uint8_t sub;
  uint32_t a;
  uint32_t b;
  uint32_t c;
};  // 14 bytes!
#pragma pack(pop)

struct NameNode {
  uint32_t pre = 0;
  std::string seg;
};

struct Decl {
  uint32_t name_id = 0;
  char kind = '?';  // 't'=thm, 'd'=def, 'o'=opaque, 'a'=axiom, 'q'=quot, 'i'=ind, 'c'=ctor, 'r'=rec
  uint32_t group_id = 0xFFFFFFFFu;  // inductive group id if i/c/r
  uint32_t type_ie = 0xFFFFFFFFu;
  uint32_t val_ie = 0xFFFFFFFFu;
};

struct IndGroup {
  std::vector<uint32_t> decl_indices;
  std::vector<uint32_t> extra_ies;  // rec rule rhs ies
};

static inline uint64_t splitmix64(uint64_t x) {
  x += 0x9e3779b97f4a7c15ULL;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}

static inline uint64_t hash_combine(uint64_t a, uint64_t b) {
  return splitmix64(a ^ (b * 0x9ddfea08eb382d69ULL));
}

// Fast integer finder after key like "\"ie\":"
static inline bool find_u32(const char* s, const char* key, uint32_t& out) {
  const char* p = std::strstr(s, key);
  if (!p) return false;
  p += std::strlen(key);
  while (*p == ' ') p++;
  if (*p < '0' || *p > '9') return false;
  uint64_t v = 0;
  while (*p >= '0' && *p <= '9') {
    v = v * 10 + (*p - '0');
    p++;
  }
  out = (uint32_t)v;
  return true;
}

static std::string parse_json_str_after(const char* p) {
  // p points just after opening '"'
  std::string out;
  while (*p && *p != '"') {
    if (*p == '\\') {
      p++;
      if (!*p) break;
      switch (*p) {
        case '"': out.push_back('"'); p++; break;
        case '\\': out.push_back('\\'); p++; break;
        case '/': out.push_back('/'); p++; break;
        case 'n': out.push_back('\n'); p++; break;
        case 'r': out.push_back('\r'); p++; break;
        case 't': out.push_back('\t'); p++; break;
        case 'u': {
          p++;
          unsigned code = 0;
          for (int k = 0; k < 4 && *p; k++, p++) {
            code <<= 4;
            if (*p >= '0' && *p <= '9') code |= (*p - '0');
            else if (*p >= 'a' && *p <= 'f') code |= (*p - 'a' + 10);
            else if (*p >= 'A' && *p <= 'F') code |= (*p - 'A' + 10);
          }
          if (code < 0x80) {
            out.push_back((char)code);
          } else if (code < 0x800) {
            out.push_back((char)(0xC0 | (code >> 6)));
            out.push_back((char)(0x80 | (code & 0x3F)));
          } else {
            out.push_back((char)(0xE0 | (code >> 12)));
            out.push_back((char)(0x80 | ((code >> 6) & 0x3F)));
            out.push_back((char)(0x80 | (code & 0x3F)));
          }
          break;
        }
        default: out.push_back(*p++); break;
      }
    } else {
      out.push_back(*p++);
    }
  }
  return out;
}

static void parse_inductive_line(const char* line, std::vector<Decl>& decls,
                                 std::vector<IndGroup>& groups,
                                 std::unordered_map<uint32_t, uint32_t>& name_to_decl) {
  uint32_t gid = (uint32_t)groups.size();
  groups.emplace_back();
  IndGroup& g = groups.back();

  // Locate sections "ctors":[ ... ],"recs":[ ... ],"types":[ ... ]
  const char* p_ctors = std::strstr(line, "\"ctors\":[");
  const char* p_recs = std::strstr(line, "\"recs\":[");
  const char* p_types = std::strstr(line, "\"types\":[");

  auto scan_decls_in_range = [&](const char* beg, const char* end, char kind) {
    if (!beg || !end || beg >= end) return;
    const char* cur = beg;
    while (cur < end) {
      const char* nm = std::strstr(cur, "\"name\":");
      if (!nm || nm >= end) break;
      uint32_t name_id = 0, type_ie = 0;
      if (find_u32(nm, "\"name\":", name_id) && find_u32(nm, "\"type\":", type_ie)) {
        uint32_t did = (uint32_t)decls.size();
        decls.push_back({name_id, kind, gid, type_ie, 0xFFFFFFFFu});
        name_to_decl[name_id] = did;
        g.decl_indices.push_back(did);
      }
      cur = nm + 7;
    }
  };

  size_t len = std::strlen(line);
  const char* end_line = line + len;
  // Order in JSON: ctors, recs, types
  scan_decls_in_range(p_ctors, p_recs ? p_recs : end_line, 'c');
  scan_decls_in_range(p_recs, p_types ? p_types : end_line, 'r');
  scan_decls_in_range(p_types, end_line, 'i');

  // Also collect all "rhs":<ie> inside recs rules
  if (p_recs) {
    const char* cur = p_recs;
    const char* stop = p_types ? p_types : end_line;
    while (cur < stop) {
      const char* r = std::strstr(cur, "\"rhs\":");
      if (!r || r >= stop) break;
      uint32_t rhs_ie = 0;
      if (find_u32(r, "\"rhs\":", rhs_ie)) {
        g.extra_ies.push_back(rhs_ie);
      }
      cur = r + 6;
    }
  }
}

int main(int argc, char** argv) {
  if (argc < 3) {
    std::cerr << "Usage: extract_dag <out_decls.tsv> <out_edges.bin> < stdin_ndjson\n";
    return 1;
  }

  std::vector<NameNode> names(1);  // 0 = anonymous root
  PagedVec<ExprNode> exprs;
  std::vector<Decl> decls;
  std::vector<IndGroup> ind_groups;
  std::unordered_map<uint32_t, uint32_t> name_to_decl;
  name_to_decl.reserve(2000000);
  decls.reserve(2000000);
  names.reserve(4000000);

  // Large line buffer (some inductive/meta lines can be tens of KB)
  std::vector<char> linebuf(16 * 1024 * 1024);
  uint64_t line_cnt = 0;

  while (std::fgets(linebuf.data(), (int)linebuf.size(), stdin)) {
    // Handle very long lines if needed
    size_t len = std::strlen(linebuf.data());
    while (len > 0 && linebuf[len - 1] != '\n' && !std::feof(stdin)) {
      size_t old_sz = linebuf.size();
      linebuf.resize(old_sz * 2);
      if (!std::fgets(linebuf.data() + len, (int)(linebuf.size() - len), stdin)) break;
      len += std::strlen(linebuf.data() + len);
    }
    const char* s = linebuf.data();
    line_cnt++;
    if ((line_cnt & 0x3FFFFFFULL) == 0) {
      std::cerr << "Parsed " << (line_cnt >> 20) << "M lines, exprs=" << exprs.size()
                << ", decls=" << decls.size() << "...\n";
    }

    // Fast dispatch on first key at s+2 (s begins with "{\"")
    if (s[0] != '{' || s[1] != '"') continue;

    // Check fast common cases:
    // "app", "ie", "forallE", "in", "const", "il", "bvar", "thm", "def", "inductive", "opaque", "quot", "axiom", "meta"
    if (std::strncmp(s + 2, "il\":", 4) == 0 || std::strncmp(s + 2, "meta\":", 6) == 0) {
      continue;
    }

    if (std::strncmp(s + 2, "in\":", 4) == 0) {
      uint32_t id = 0, pre = 0;
      find_u32(s + 1, "\"in\":", id);
      find_u32(s + 5, "\"pre\":", pre);
      if (id >= names.size()) names.resize(id + 1);
      const char* sp = std::strstr(s + 6, "\"str\":{\"pre\":");
      if (sp) {
        const char* valq = std::strstr(sp + 13, "\"str\":\"");
        if (valq) {
          names[id] = {pre, parse_json_str_after(valq + 7)};
        }
      } else {
        uint32_t num_i = 0;
        find_u32(s + 5, "\"i\":", num_i);
        names[id] = {pre, std::to_string(num_i)};
      }
      continue;
    }

    // Check expression lines
    if (std::strncmp(s + 2, "app\":", 5) == 0) {
      uint32_t arg = 0, fn = 0, ie = 0;
      find_u32(s + 6, "\"arg\":", arg);
      find_u32(s + 6, "\"fn\":", fn);
      find_u32(s + 6, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_BINARY, 0, fn, arg, 0};
      continue;
    }
    if (std::strncmp(s + 2, "forallE\":", 9) == 0) {
      uint32_t body = 0, type = 0, ie = 0;
      find_u32(s + 10, "\"body\":", body);
      find_u32(s + 10, "\"type\":", type);
      find_u32(s + 10, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_BINARY, 2, type, body, 0};
      continue;
    }
    if (std::strncmp(s + 2, "const\":", 7) == 0) {
      uint32_t nm = 0, ie = 0;
      find_u32(s + 8, "\"name\":", nm);
      find_u32(s + 8, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_CONST, 0, nm, 0, 0};
      continue;
    }
    if (std::strncmp(s + 2, "bvar\":", 6) == 0) {
      uint32_t bv = 0, ie = 0;
      find_u32(s + 1, "\"bvar\":", bv);
      find_u32(s + 7, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_LEAF, 1, bv, 0, 0};
      continue;
    }
    if (std::strncmp(s + 2, "ie\":", 4) == 0) {
      uint32_t ie = 0;
      find_u32(s + 1, "\"ie\":", ie);
      exprs.ensure(ie);
      if (const char* p = std::strstr(s + 6, "\"lam\":")) {
        uint32_t body = 0, type = 0;
        find_u32(p, "\"body\":", body);
        find_u32(p, "\"type\":", type);
        exprs[ie] = {EK_BINARY, 1, type, body, 0};
      } else if (const char* p = std::strstr(s + 6, "\"letE\":")) {
        uint32_t body = 0, type = 0, val = 0;
        find_u32(p, "\"body\":", body);
        find_u32(p, "\"type\":", type);
        find_u32(p, "\"value\":", val);
        exprs[ie] = {EK_LET, 0, type, val, body};
      } else if (const char* p = std::strstr(s + 6, "\"proj\":")) {
        uint32_t idx = 0, st = 0, tn = 0;
        find_u32(p, "\"idx\":", idx);
        find_u32(p, "\"struct\":", st);
        find_u32(p, "\"typeName\":", tn);
        exprs[ie] = {EK_PROJ, 0, st, tn, idx};
      } else if (const char* p = std::strstr(s + 6, "\"mdata\":")) {
        uint32_t ex = 0;
        find_u32(p, "\"expr\":", ex);
        exprs[ie] = {EK_UNARY, 0, ex, 0, 0};
      } else if (std::strstr(s + 6, "\"sort\":")) {
        exprs[ie] = {EK_LEAF, 0, 0, 0, 0};
      } else {
        // natVal / strVal literal: hash string
        uint64_t h = splitmix64(std::hash<std::string_view>{}(std::string_view(s + 6)));
        exprs[ie] = {EK_LEAF, 2, (uint32_t)h, (uint32_t)(h >> 32), 0};
      }
      continue;
    }

    // Declaration lines
    if (std::strncmp(s + 2, "thm\":", 5) == 0 ||
        std::strncmp(s + 2, "def\":", 5) == 0 ||
        std::strncmp(s + 2, "opaque\":", 8) == 0) {
      char k = s[2];  // 't', 'd', 'o'
      uint32_t nm = 0, tp = 0, vl = 0;
      find_u32(s + 5, "\"name\":", nm);
      find_u32(s + 5, "\"type\":", tp);
      find_u32(s + 5, "\"value\":", vl);
      uint32_t did = (uint32_t)decls.size();
      decls.push_back({nm, k, 0xFFFFFFFFu, tp, vl});
      name_to_decl[nm] = did;
      continue;
    }
    if (std::strncmp(s + 2, "axiom\":", 7) == 0 ||
        std::strncmp(s + 2, "quot\":", 6) == 0) {
      char k = s[2];  // 'a', 'q'
      uint32_t nm = 0, tp = 0;
      find_u32(s + 5, "\"name\":", nm);
      find_u32(s + 5, "\"type\":", tp);
      uint32_t did = (uint32_t)decls.size();
      decls.push_back({nm, k, 0xFFFFFFFFu, tp, 0xFFFFFFFFu});
      name_to_decl[nm] = did;
      continue;
    }
    if (std::strncmp(s + 2, "inductive\":", 11) == 0) {
      parse_inductive_line(s, decls, ind_groups, name_to_decl);
      continue;
    }
  }

  std::cerr << "Done reading: lines=" << line_cnt
            << ", names=" << names.size()
            << ", exprs=" << exprs.size()
            << ", decls=" << decls.size() << "\n";

  // Helper to reconstruct full name string
  auto get_full_name = [&](uint32_t nid) -> std::string {
    std::vector<const std::string*> segs;
    uint32_t cur = nid;
    while (cur != 0 && cur < names.size()) {
      segs.push_back(&names[cur].seg);
      cur = names[cur].pre;
    }
    std::string res;
    for (auto it = segs.rbegin(); it != segs.rend(); ++it) {
      if (!res.empty()) res.push_back('.');
      res += **it;
    }
    return res;
  };

  // Map full string names of root targets to decl indices
  std::unordered_map<std::string, uint32_t> str_to_decl;
  std::vector<std::string> decl_names(decls.size());
  for (size_t i = 0; i < decls.size(); i++) {
    decl_names[i] = get_full_name(decls[i].name_id);
    str_to_decl[decl_names[i]] = (uint32_t)i;
  }

  // Bipartite BFS helper
  auto run_bfs = [&](const std::vector<std::string>& roots, bool stmt_only) {
    std::vector<uint8_t> vis_decl(decls.size(), 0);
    PagedVec<uint8_t> vis_expr;
    if (exprs.size() > 0) vis_expr.ensure(exprs.size() - 1);
    std::vector<uint8_t> vis_group(ind_groups.size(), 0);

    std::vector<uint32_t> q_decl;
    std::vector<uint32_t> q_expr;

    auto push_expr = [&](uint32_t ie) {
      if (ie != 0xFFFFFFFFu && ie < exprs.size() && !vis_expr[ie]) {
        vis_expr[ie] = 1;
        q_expr.push_back(ie);
      }
    };
    auto push_decl = [&](uint32_t did) {
      if (did < decls.size() && !vis_decl[did]) {
        vis_decl[did] = 1;
        q_decl.push_back(did);
      }
    };

    for (const auto& r : roots) {
      auto it = str_to_decl.find(r);
      if (it != str_to_decl.end()) {
        push_decl(it->second);
      } else {
        std::cerr << "WARNING: root not found: " << r << "\n";
      }
    }

    while (!q_decl.empty() || !q_expr.empty()) {
      while (!q_decl.empty()) {
        uint32_t did = q_decl.back();
        q_decl.pop_back();
        const Decl& d = decls[did];
        push_expr(d.type_ie);
        if (!stmt_only || d.kind != 't') {
          push_expr(d.val_ie);
        }
        if (d.group_id != 0xFFFFFFFFu && !vis_group[d.group_id]) {
          vis_group[d.group_id] = 1;
          for (uint32_t m : ind_groups[d.group_id].decl_indices) push_decl(m);
          for (uint32_t e : ind_groups[d.group_id].extra_ies) push_expr(e);
        }
      }
      while (!q_expr.empty()) {
        uint32_t ie = q_expr.back();
        q_expr.pop_back();
        const ExprNode& e = exprs[ie];
        switch (e.kind) {
          case EK_UNARY:
            push_expr(e.a);
            break;
          case EK_BINARY:
            push_expr(e.a);
            push_expr(e.b);
            break;
          case EK_LET:
            push_expr(e.a);
            push_expr(e.b);
            push_expr(e.c);
            break;
          case EK_CONST: {
            auto it = name_to_decl.find(e.a);
            if (it != name_to_decl.end()) push_decl(it->second);
            break;
          }
          case EK_PROJ: {
            push_expr(e.a);
            auto it = name_to_decl.find(e.b);
            if (it != name_to_decl.end()) push_decl(it->second);
            break;
          }
          default:
            break;
        }
      }
    }
    size_t cnt_d = 0, cnt_e = 0;
    for (uint8_t v : vis_decl) cnt_d += v;
    for (size_t i = 0; i < exprs.size(); i++) cnt_e += vis_expr[i];
    std::cerr << "BFS(stmt_only=" << stmt_only << ", roots=" << roots.size()
              << "): decls=" << cnt_d << ", exprs=" << cnt_e << "\n";
    return vis_decl;
  };

  std::vector<std::string> all5_roots = {
      "riemannHypothesis",
      "riemannZeta_eq_zero_re",
      "LFunction_ne_zero_of_half_lt_re",
      "LFunction_eq_zero_re",
      "LFunction_eq_zero_re_of_isPrimitive"};
  std::vector<std::string> rh_roots = {"riemannHypothesis"};

  auto in_all5 = run_bfs(all5_roots, false);
  auto in_rh = run_bfs(rh_roots, false);
  auto in_rh_stmt = run_bfs(rh_roots, true);

  // Compute universe-erased 64-bit structural hash of every ExprNode bottom-up!
  std::cerr << "Computing bottom-up universe-erased structural hashes...\n";
  std::vector<uint64_t> decl_type_hash(decls.size(), 0);
  {
    PagedVec<uint64_t> ehash;
    if (exprs.size() > 0) ehash.ensure(exprs.size() - 1);
    for (size_t ie = 0; ie < exprs.size(); ie++) {
      const ExprNode& e = exprs[ie];
      uint64_t h = splitmix64(((uint64_t)e.kind << 8) | e.sub);
      switch (e.kind) {
        case EK_LEAF:
          h = hash_combine(h, ((uint64_t)e.b << 32) | e.a);
          break;
        case EK_UNARY:
          h = hash_combine(h, e.a < ie ? ehash[e.a] : e.a);
          break;
        case EK_BINARY:
          h = hash_combine(h, e.a < ie ? ehash[e.a] : e.a);
          h = hash_combine(h, e.b < ie ? ehash[e.b] : e.b);
          break;
        case EK_LET:
          h = hash_combine(h, e.a < ie ? ehash[e.a] : e.a);
          h = hash_combine(h, e.b < ie ? ehash[e.b] : e.b);
          h = hash_combine(h, e.c < ie ? ehash[e.c] : e.c);
          break;
        case EK_CONST:
          h = hash_combine(h, e.a);
          break;
        case EK_PROJ:
          h = hash_combine(h, e.a < ie ? ehash[e.a] : e.a);
          h = hash_combine(h, ((uint64_t)e.c << 32) | e.b);
          break;
        default:
          break;
      }
      ehash[ie] = h;
    }
    for (size_t i = 0; i < decls.size(); i++) {
      if (decls[i].type_ie < exprs.size()) decl_type_hash[i] = ehash[decls[i].type_ie];
    }
  }  // ehash freed here!

  // Extract direct decl->decl constant dependencies (separately for type and value) + own_expr_nodes!
  // Binary format of out_edges.bin:
  //   uint32_t num_decls;
  //   For each decl i in 0..num_decls-1:
  //     uint32_t num_type_deps;
  //     uint32_t type_deps[num_type_deps];
  //     uint32_t num_val_deps;
  //     uint32_t val_deps[num_val_deps];
  std::cerr << "Extracting direct declaration dependency DAG...\n";
  std::vector<uint32_t> own_nodes(decls.size(), 0);
  {
    PagedVec<uint32_t> stamp;
    if (exprs.size() > 0) stamp.ensure(exprs.size() - 1);
    std::vector<uint32_t> d_stamp(decls.size(), 0);
    uint32_t cur_tag = 0;
    uint64_t total_visits = 0;

    FILE* efp = std::fopen(argv[2], "wb");
    uint32_t nd = (uint32_t)decls.size();
    std::fwrite(&nd, sizeof(uint32_t), 1, efp);

    std::vector<uint32_t> st;
    std::vector<uint32_t> deps;

    auto collect = [&](const std::vector<uint32_t>& roots, uint32_t self_did, uint32_t& node_cnt) {
      cur_tag++;
      deps.clear();
      st.clear();
      for (uint32_t r : roots) {
        if (r != 0xFFFFFFFFu && r < exprs.size() && stamp[r] != cur_tag) {
          stamp[r] = cur_tag;
          st.push_back(r);
        }
      }
      while (!st.empty()) {
        uint32_t ie = st.back();
        st.pop_back();
        node_cnt++;
        total_visits++;
        const ExprNode& e = exprs[ie];
        auto push = [&](uint32_t ch) {
          if (ch != 0xFFFFFFFFu && ch < exprs.size() && stamp[ch] != cur_tag) {
            stamp[ch] = cur_tag;
            st.push_back(ch);
          }
        };
        auto add_const = [&](uint32_t nid) {
          auto it = name_to_decl.find(nid);
          if (it != name_to_decl.end() && it->second != self_did && d_stamp[it->second] != cur_tag) {
            d_stamp[it->second] = cur_tag;
            deps.push_back(it->second);
          }
        };
        switch (e.kind) {
          case EK_UNARY: push(e.a); break;
          case EK_BINARY: push(e.a); push(e.b); break;
          case EK_LET: push(e.a); push(e.b); push(e.c); break;
          case EK_CONST: add_const(e.a); break;
          case EK_PROJ: push(e.a); add_const(e.b); break;
          default: break;
        }
      }
    };

    for (size_t i = 0; i < decls.size(); i++) {
      const Decl& d = decls[i];
      uint32_t ncnt = 0;
      collect({d.type_ie}, (uint32_t)i, ncnt);
      uint32_t nt = (uint32_t)deps.size();
      std::fwrite(&nt, sizeof(uint32_t), 1, efp);
      if (nt) std::fwrite(deps.data(), sizeof(uint32_t), nt, efp);

      std::vector<uint32_t> vroots;
      if (d.val_ie != 0xFFFFFFFFu) vroots.push_back(d.val_ie);
      if (d.group_id != 0xFFFFFFFFu && d.kind == 'r') {
        for (uint32_t ex : ind_groups[d.group_id].extra_ies) vroots.push_back(ex);
      }
      collect(vroots, (uint32_t)i, ncnt);
      if (d.group_id != 0xFFFFFFFFu) {
        for (uint32_t m : ind_groups[d.group_id].decl_indices) {
          if (m != i && std::find(deps.begin(), deps.end(), m) == deps.end()) deps.push_back(m);
        }
      }
      uint32_t nv = (uint32_t)deps.size();
      std::fwrite(&nv, sizeof(uint32_t), 1, efp);
      if (nv) std::fwrite(deps.data(), sizeof(uint32_t), nv, efp);
      own_nodes[i] = ncnt;
    }
    std::fclose(efp);
    std::cerr << "Direct DAG extracted! total_expr_visits=" << total_visits
              << " (ratio=" << (exprs.size() ? (double)total_visits / exprs.size() : 0.0) << "x)\n";
  }

  std::cerr << "Writing output TSV to " << argv[1] << "...\n";
  std::ofstream out(argv[1]);
  out << "decl_id\tkind\tin_all5\tin_rh\tin_rh_stmt\ttype_ie\tval_ie\town_nodes\ttype_hash\tname\n";
  char hexbuf[32];
  for (size_t i = 0; i < decls.size(); i++) {
    const Decl& d = decls[i];
    std::snprintf(hexbuf, sizeof(hexbuf), "%016llx", (unsigned long long)decl_type_hash[i]);
    out << i << '\t' << d.kind << '\t'
        << (int)in_all5[i] << '\t' << (int)in_rh[i] << '\t' << (int)in_rh_stmt[i] << '\t'
        << d.type_ie << '\t' << d.val_ie << '\t' << own_nodes[i] << '\t'
        << hexbuf << '\t' << decl_names[i] << '\n';
  }
  std::cerr << "All done!\n";
  return 0;
}
