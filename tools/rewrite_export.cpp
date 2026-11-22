#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

template <typename T, size_t PAGE_BITS = 23>
struct PagedVec {
  static constexpr size_t PAGE_SIZE = size_t(1) << PAGE_BITS;
  static constexpr size_t PAGE_MASK = PAGE_SIZE - 1;
  std::vector<T*> pages;
  size_t sz = 0;

  ~PagedVec() { clear_and_free(); }
  PagedVec() = default;
  PagedVec(const PagedVec&) = delete;
  PagedVec& operator=(const PagedVec&) = delete;

  void clear_and_free() {
    for (T* p : pages) delete[] p;
    pages.clear();
    sz = 0;
  }

  void ensure(size_t idx) {
    while ((idx >> PAGE_BITS) >= pages.size()) {
      pages.push_back(new T[PAGE_SIZE]());
    }
    if (idx + 1 > sz) sz = idx + 1;
  }

  T& operator[](size_t idx) { return pages[idx >> PAGE_BITS][idx & PAGE_MASK]; }
  const T& operator[](size_t idx) const { return pages[idx >> PAGE_BITS][idx & PAGE_MASK]; }
  size_t size() const { return sz; }
};

enum ExprKind : uint8_t {
  EK_NONE = 0,
  EK_LEAF = 1,
  EK_UNARY = 2,
  EK_BINARY = 3,
  EK_LET = 4,
  EK_CONST = 5,
  EK_PROJ = 6
};

#pragma pack(push, 1)
struct ExprNode {
  uint8_t kind;
  uint32_t a;
  uint32_t b;
  uint32_t c;
};  // 13 bytes!
#pragma pack(pop)

struct NameNode {
  uint32_t pre = 0;
  std::string seg;
};

struct Decl {
  uint32_t name_id = 0;
  char kind = '?';
  uint32_t group_id = 0xFFFFFFFFu;
  uint32_t type_ie = 0xFFFFFFFFu;
  uint32_t val_ie = 0xFFFFFFFFu;
  bool single_all = false;
  std::string sig_key;  // for CSE: exact raw levelParams (+ hints/safety for def)
};

struct IndGroup {
  std::vector<uint32_t> decl_indices;
  std::vector<uint32_t> extra_ies;
};

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

static std::string extract_bracket_slice(const char* s, const char* key) {
  const char* p = std::strstr(s, key);
  if (!p) return "";
  p += std::strlen(key);
  if (*p != '[' && *p != '{' && *p != '"') return "";
  char open = *p;
  if (open == '"') {
    const char* q = p + 1;
    while (*q && *q != '"') {
      if (*q == '\\' && *(q + 1)) q += 2;
      else q++;
    }
    return std::string(p, (q - p) + (*q == '"' ? 1 : 0));
  }
  char close = (open == '[') ? ']' : '}';
  int depth = 1;
  const char* q = p + 1;
  while (*q && depth > 0) {
    if (*q == open) depth++;
    else if (*q == close) depth--;
    q++;
  }
  return std::string(p, q - p);
}

static std::string parse_json_str_after(const char* p) {
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
          if (code < 0x80) out.push_back((char)code);
          else if (code < 0x800) {
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
  const char* p_ctors = std::strstr(line, "\"ctors\":[");
  const char* p_recs = std::strstr(line, "\"recs\":[");
  const char* p_types = std::strstr(line, "\"types\":[");
  size_t len = std::strlen(line);
  const char* end_line = line + len;

  auto scan_range = [&](const char* beg, const char* end, char kind) {
    if (!beg || !end || beg >= end) return;
    const char* cur = beg;
    while (cur < end) {
      const char* nm = std::strstr(cur, "\"name\":");
      if (!nm || nm >= end) break;
      uint32_t nid = 0, tie = 0;
      if (find_u32(nm, "\"name\":", nid) && find_u32(nm, "\"type\":", tie)) {
        uint32_t did = (uint32_t)decls.size();
        decls.push_back({nid, kind, gid, tie, 0xFFFFFFFFu, false, ""});
        name_to_decl[nid] = did;
        g.decl_indices.push_back(did);
      }
      cur = nm + 7;
    }
  };
  scan_range(p_ctors, p_recs ? p_recs : end_line, 'c');
  scan_range(p_recs, p_types ? p_types : end_line, 'r');
  scan_range(p_types, end_line, 'i');

  if (p_recs) {
    const char* cur = p_recs;
    const char* stop = p_types ? p_types : end_line;
    while (cur < stop) {
      const char* r = std::strstr(cur, "\"rhs\":");
      if (!r || r >= stop) break;
      uint32_t rhs_ie = 0;
      if (find_u32(r, "\"rhs\":", rhs_ie)) g.extra_ies.push_back(rhs_ie);
      cur = r + 6;
    }
  }
}

// Replace numeric value immediately after exact key `key` inside `line`, non-overlapping, left-to-right!
// For inductive lines, replaces all `"type":<u32>` and `"rhs":<u32>`.
static std::string rewrite_u32_keys(std::string_view line,
                                    const std::vector<std::pair<std::string_view, bool>>& keys_is_expr,
                                    const PagedVec<uint32_t>& remap_ie,
                                    const std::unordered_map<uint32_t, uint32_t>& redirect_name) {
  std::string out;
  out.reserve(line.size() + 16);
  size_t i = 0;
  bool in_str = false;
  while (i < line.size()) {
    if (in_str) {
      if (line[i] == '\\' && i + 1 < line.size()) {
        out.push_back(line[i]);
        out.push_back(line[i + 1]);
        i += 2;
        continue;
      }
      if (line[i] == '"') in_str = false;
      out.push_back(line[i++]);
      continue;
    }
    if (line[i] == '"') {
      // Check if any key starts here!
      bool matched = false;
      for (const auto& [k, is_expr] : keys_is_expr) {
        if (i + k.size() <= line.size() && line.substr(i, k.size()) == k) {
          size_t j = i + k.size();
          if (j < line.size() && line[j] >= '0' && line[j] <= '9') {
            uint64_t val = 0;
            while (j < line.size() && line[j] >= '0' && line[j] <= '9') {
              val = val * 10 + (line[j] - '0');
              j++;
            }
            out.append(k);
            uint32_t old_id = (uint32_t)val;
            uint32_t new_id = old_id;
            if (is_expr) {
              new_id = remap_ie[old_id];
            } else {
              auto it = redirect_name.find(old_id);
              if (it != redirect_name.end()) new_id = it->second;
            }
            out.append(std::to_string(new_id));
            i = j;
            matched = true;
            break;
          }
        }
      }
      if (matched) continue;
      in_str = true;
      out.push_back(line[i++]);
      continue;
    }
    out.push_back(line[i++]);
  }
  return out;
}

int main(int argc, char** argv) {
  if (argc < 4) {
    std::cerr << "Usage: rewrite_export <input.ndjson.zst | input.ndjson> <challenge_decls.tsv> <output.ndjson> [--long30]\n";
    return 1;
  }
  std::string in_path = argv[1];
  std::string chal_tsv = argv[2];
  std::string out_path = argv[3];
  bool is_zst = (in_path.size() > 4 && in_path.substr(in_path.size() - 4) == ".zst");

  auto open_stream = [&]() -> FILE* {
    if (is_zst) {
      std::string cmd = "zstd -dc --long=30 \"" + in_path + "\"";
      return popen(cmd.c_str(), "r");
    }
    return std::fopen(in_path.c_str(), "rb");
  };
  auto close_stream = [&](FILE* f) {
    if (is_zst) pclose(f);
    else std::fclose(f);
  };

  // Load protected names from challenge_decls.tsv
  std::unordered_set<std::string> protected_names;
  {
    std::ifstream in(chal_tsv);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      size_t tab = line.rfind('\t');
      if (tab != std::string::npos) protected_names.insert(line.substr(tab + 1));
    }
  }
  // Ensure all 5 headline theorems + standard kernel pins are protected
  for (const char* s : {
           "riemannHypothesis", "riemannZeta_eq_zero_re",
           "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
           "LFunction_eq_zero_re_of_isPrimitive",
           "Nat.add", "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.pow",
           "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
           "Nat.shiftLeft", "Nat.shiftRight", "Nat.gcd",
           "String.mk", "String.mk._proof_1"}) {
    protected_names.insert(s);
  }
  std::cerr << "Protected baseline names: " << protected_names.size() << "\n";

  // ===================== PASS 1: Read & Build Graph =====================
  std::cerr << "=== PASS 1: Streaming " << in_path << " ===\n";
  std::vector<NameNode> names(1);
  PagedVec<ExprNode> exprs;
  std::vector<Decl> decls;
  std::vector<IndGroup> ind_groups;
  std::unordered_map<uint32_t, uint32_t> name_to_decl;
  names.reserve(15000000);
  decls.reserve(1600000);
  name_to_decl.reserve(1600000);

  std::vector<char> linebuf(16 * 1024 * 1024);
  FILE* fp1 = open_stream();
  if (!fp1) { std::perror("open_stream pass1"); return 1; }
  uint64_t line_cnt = 0;

  while (std::fgets(linebuf.data(), (int)linebuf.size(), fp1)) {
    size_t len = std::strlen(linebuf.data());
    while (len > 0 && linebuf[len - 1] != '\n' && !std::feof(fp1)) {
      linebuf.resize(linebuf.size() * 2);
      if (!std::fgets(linebuf.data() + len, (int)(linebuf.size() - len), fp1)) break;
      len += std::strlen(linebuf.data() + len);
    }
    const char* s = linebuf.data();
    line_cnt++;
    if ((line_cnt & 0x7FFFFFFULL) == 0) {
      std::cerr << "  Pass 1: " << (line_cnt >> 20) << "M lines, exprs=" << exprs.size() << ", decls=" << decls.size() << "\n";
    }
    if (s[0] != '{' || s[1] != '"') continue;
    if (std::strncmp(s + 2, "il\":", 4) == 0 || std::strncmp(s + 2, "meta\":", 6) == 0) continue;

    if (std::strncmp(s + 2, "in\":", 4) == 0) {
      uint32_t id = 0, pre = 0;
      find_u32(s + 1, "\"in\":", id);
      find_u32(s + 5, "\"pre\":", pre);
      if (id >= names.size()) names.resize(id + 1);
      const char* sp = std::strstr(s + 6, "\"str\":{\"pre\":");
      if (sp) {
        const char* valq = std::strstr(sp + 13, "\"str\":\"");
        if (valq) names[id] = {pre, parse_json_str_after(valq + 7)};
      } else {
        uint32_t num_i = 0;
        find_u32(s + 5, "\"i\":", num_i);
        names[id] = {pre, std::to_string(num_i)};
      }
      continue;
    }

    if (std::strncmp(s + 2, "app\":", 5) == 0) {
      uint32_t arg = 0, fn = 0, ie = 0;
      find_u32(s + 6, "\"arg\":", arg);
      find_u32(s + 6, "\"fn\":", fn);
      find_u32(s + 6, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_BINARY, fn, arg, 0};
      continue;
    }
    if (std::strncmp(s + 2, "forallE\":", 9) == 0) {
      uint32_t body = 0, type = 0, ie = 0;
      find_u32(s + 10, "\"body\":", body);
      find_u32(s + 10, "\"type\":", type);
      find_u32(s + 10, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_BINARY, type, body, 0};
      continue;
    }
    if (std::strncmp(s + 2, "const\":", 7) == 0) {
      uint32_t nm = 0, ie = 0;
      find_u32(s + 8, "\"name\":", nm);
      find_u32(s + 8, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_CONST, nm, 0, 0};
      continue;
    }
    if (std::strncmp(s + 2, "bvar\":", 6) == 0) {
      uint32_t ie = 0;
      find_u32(s + 7, "\"ie\":", ie);
      exprs.ensure(ie);
      exprs[ie] = {EK_LEAF, 0, 0, 0};
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
        exprs[ie] = {EK_BINARY, type, body, 0};
      } else if (const char* p = std::strstr(s + 6, "\"letE\":")) {
        uint32_t body = 0, type = 0, val = 0;
        find_u32(p, "\"body\":", body);
        find_u32(p, "\"type\":", type);
        find_u32(p, "\"value\":", val);
        exprs[ie] = {EK_LET, type, val, body};
      } else if (const char* p = std::strstr(s + 6, "\"proj\":")) {
        uint32_t st = 0, tn = 0;
        find_u32(p, "\"struct\":", st);
        find_u32(p, "\"typeName\":", tn);
        exprs[ie] = {EK_PROJ, st, tn, 0};
      } else if (const char* p = std::strstr(s + 6, "\"mdata\":")) {
        uint32_t ex = 0;
        find_u32(p, "\"expr\":", ex);
        exprs[ie] = {EK_UNARY, ex, 0, 0};
      } else {
        exprs[ie] = {EK_LEAF, 0, 0, 0};
      }
      continue;
    }

    if (std::strncmp(s + 2, "thm\":", 5) == 0 ||
        std::strncmp(s + 2, "def\":", 5) == 0 ||
        std::strncmp(s + 2, "opaque\":", 8) == 0) {
      char k = s[2];
      uint32_t nm = 0, tp = 0, vl = 0;
      find_u32(s + 5, "\"name\":", nm);
      find_u32(s + 5, "\"type\":", tp);
      find_u32(s + 5, "\"value\":", vl);
      std::string all_s = extract_bracket_slice(s + 5, "\"all\":");
      bool single_all = (all_s == "[" + std::to_string(nm) + "]");
      std::string lp_s = extract_bracket_slice(s + 5, "\"levelParams\":");
      std::string sig;
      if (k == 't') {
        sig = lp_s + "|" + std::to_string(tp);
      } else if (k == 'd') {
        std::string hints_s = extract_bracket_slice(s + 5, "\"hints\":");
        std::string safe_s = extract_bracket_slice(s + 5, "\"safety\":");
        sig = lp_s + "|" + std::to_string(tp) + "|" + std::to_string(vl) + "|" + hints_s + "|" + safe_s;
      }
      uint32_t did = (uint32_t)decls.size();
      decls.push_back({nm, k, 0xFFFFFFFFu, tp, vl, single_all, std::move(sig)});
      name_to_decl[nm] = did;
      continue;
    }
    if (std::strncmp(s + 2, "axiom\":", 7) == 0 ||
        std::strncmp(s + 2, "quot\":", 6) == 0) {
      char k = s[2];
      uint32_t nm = 0, tp = 0;
      find_u32(s + 5, "\"name\":", nm);
      find_u32(s + 5, "\"type\":", tp);
      uint32_t did = (uint32_t)decls.size();
      decls.push_back({nm, k, 0xFFFFFFFFu, tp, 0xFFFFFFFFu, true, ""});
      name_to_decl[nm] = did;
      continue;
    }
    if (std::strncmp(s + 2, "inductive\":", 11) == 0) {
      parse_inductive_line(s, decls, ind_groups, name_to_decl);
      continue;
    }
  }
  close_stream(fp1);

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

  std::vector<uint8_t> is_protected(decls.size(), 0);
  std::vector<uint32_t> root_dids;
  for (size_t i = 0; i < decls.size(); i++) {
    std::string fn = get_full_name(decls[i].name_id);
    // Protect all challenge baseline names AND all Nat.* / String.* / UInt* / Fin.* core pin groundings!
    if (protected_names.count(fn) ||
        fn.compare(0, 4, "Nat.") == 0 ||
        fn.compare(0, 7, "String.") == 0 ||
        fn.compare(0, 5, "Char.") == 0 ||
        fn.compare(0, 4, "Fin.") == 0 ||
        fn.compare(0, 5, "UInt") == 0 ||
        fn.compare(0, 12, "WellFounded.") == 0 ||
        fn.compare(0, 4, "Acc.") == 0) {
      is_protected[i] = 1;
    }
    if (fn == "riemannHypothesis" ||
        fn == "riemannZeta_eq_zero_re" ||
        fn == "LFunction_ne_zero_of_half_lt_re" ||
        fn == "LFunction_eq_zero_re" ||
        fn == "LFunction_eq_zero_re_of_isPrimitive" ||
        fn == "Nat.lor" || fn == "Nat.xor" ||
        fn == "String.mk" || fn == "String.mk._proof_1") {
      root_dids.push_back((uint32_t)i);
    }
  }
  // Free `names` vector now to save ~500 MB RAM!
  { std::vector<NameNode>().swap(names); }

  // Compute exact CSE redirects (strictly to earlier declaration with identical sig_key!)
  std::unordered_map<std::string, uint32_t> first_thm_sig, first_def_sig;
  std::unordered_map<uint32_t, uint32_t> redirect_name;  // old_name_id -> winning_name_id
  size_t thm_redirects = 0, def_redirects = 0;

  for (size_t i = 0; i < decls.size(); i++) {
    const Decl& d = decls[i];
    if (!d.single_all || d.sig_key.empty()) continue;
    if (d.kind == 't') {
      auto [it, ins] = first_thm_sig.emplace(d.sig_key, d.name_id);
      if (!ins && !is_protected[i]) {
        redirect_name[d.name_id] = it->second;
        thm_redirects++;
      }
    } else if (d.kind == 'd') {
      // Only redirect defs if non-protected AND never touch Init/Core defs (thm Prop CSE is 100% proof-irrelevant everywhere!)
      auto [it, ins] = first_def_sig.emplace(d.sig_key, d.name_id);
      if (!ins && !is_protected[i]) {
        redirect_name[d.name_id] = it->second;
        def_redirects++;
      }
    }
  }
  // Free sig_keys
  {
    first_thm_sig.clear();
    first_def_sig.clear();
    for (auto& d : decls) std::string().swap(d.sig_key);
  }
  std::cerr << "Exact kernel-safe CSE candidates: " << thm_redirects << " thms, " << def_redirects << " defs.\n";

  // Bipartite GC BFS with call-site name redirection!
  std::vector<uint8_t> vis_decl(decls.size(), 0);
  std::vector<uint8_t> vis_group(ind_groups.size(), 0);
  PagedVec<uint8_t> vis_expr;
  if (exprs.size() > 0) vis_expr.ensure(exprs.size() - 1);

  std::vector<uint32_t> q_decl, q_expr;
  auto push_decl = [&](uint32_t did) {
    if (did < decls.size() && !vis_decl[did]) {
      vis_decl[did] = 1;
      q_decl.push_back(did);
    }
  };
  auto push_expr = [&](uint32_t ie) {
    if (ie != 0xFFFFFFFFu && ie < exprs.size() && !vis_expr[ie]) {
      vis_expr[ie] = 1;
      q_expr.push_back(ie);
    }
  };

  for (uint32_t r : root_dids) push_decl(r);

  while (!q_decl.empty() || !q_expr.empty()) {
    while (!q_decl.empty()) {
      uint32_t did = q_decl.back();
      q_decl.pop_back();
      const Decl& d = decls[did];
      push_expr(d.type_ie);
      push_expr(d.val_ie);
      if (d.group_id != 0xFFFFFFFFu && !vis_group[d.group_id]) {
        vis_group[d.group_id] = 1;
        for (uint32_t m : ind_groups[d.group_id].decl_indices) push_decl(m);
        for (uint32_t ex : ind_groups[d.group_id].extra_ies) push_expr(ex);
      }
    }
    while (!q_expr.empty()) {
      uint32_t ie = q_expr.back();
      q_expr.pop_back();
      const ExprNode& e = exprs[ie];
      switch (e.kind) {
        case EK_UNARY: push_expr(e.a); break;
        case EK_BINARY: push_expr(e.a); push_expr(e.b); break;
        case EK_LET: push_expr(e.a); push_expr(e.b); push_expr(e.c); break;
        case EK_CONST: {
          uint32_t nid = e.a;
          auto rit = redirect_name.find(nid);
          if (rit != redirect_name.end()) nid = rit->second;
          auto dit = name_to_decl.find(nid);
          if (dit != name_to_decl.end()) push_decl(dit->second);
          break;
        }
        case EK_PROJ: {
          push_expr(e.a);
          auto dit = name_to_decl.find(e.b);
          if (dit != name_to_decl.end()) push_decl(dit->second);
          break;
        }
        default: break;
      }
    }
  }

  size_t old_expr_cnt = exprs.size();
  exprs.clear_and_free();

  PagedVec<uint32_t> remap_ie;
  if (old_expr_cnt > 0) remap_ie.ensure(old_expr_cnt - 1);
  uint32_t new_expr_cnt = 0;
  for (size_t ie = 0; ie < old_expr_cnt; ie++) {
    if (vis_expr[ie]) {
      remap_ie[ie] = new_expr_cnt++;
    }
  }
  size_t kept_decls = 0;
  for (uint8_t v : vis_decl) kept_decls += v;

  std::cerr << "GC Summary:\n"
            << "  Declarations: " << decls.size() << " -> " << kept_decls
            << " (-" << (decls.size() - kept_decls) << ", -"
            << (100.0 * (decls.size() - kept_decls) / decls.size()) << "%)\n"
            << "  Expressions:  " << old_expr_cnt << " -> " << new_expr_cnt
            << " (-" << (old_expr_cnt - new_expr_cnt) << ", -"
            << (100.0 * (old_expr_cnt - new_expr_cnt) / old_expr_cnt) << "%)\n";

  // ===================== PASS 2: Stream & Emit Shrunk NDJSON =====================
  std::cerr << "=== PASS 2: Writing shrunk export to " << out_path << " ===\n";
  FILE* fp2 = open_stream();
  FILE* out_fp = std::fopen(out_path.c_str(), "wb");
  if (!fp2 || !out_fp) { std::perror("open pass2"); return 1; }
  // 8 MB stdio output buffer
  std::vector<char> outbuf(8 * 1024 * 1024);
  std::setvbuf(out_fp, outbuf.data(), _IOFBF, outbuf.size());

  const std::vector<std::pair<std::string_view, bool>> k_app = {
      {"\"arg\":", true}, {"\"fn\":", true}, {"\"ie\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_lam_forall = {
      {"\"body\":", true}, {"\"type\":", true}, {"\"ie\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_let = {
      {"\"body\":", true}, {"\"type\":", true}, {"\"value\":", true}, {"\"ie\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_const = {
      {"\"name\":", false}, {"\"ie\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_proj = {
      {"\"struct\":", true}, {"\"ie\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_mdata = {
      {"\"expr\":", true}, {"\"ie\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_ie_only = {
      {"\"ie\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_decl_tv = {
      {"\"type\":", true}, {"\"value\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_decl_t = {
      {"\"type\":", true}};
  const std::vector<std::pair<std::string_view, bool>> k_ind = {
      {"\"type\":", true}, {"\"rhs\":", true}};

  uint64_t p2_lines = 0, out_lines = 0;
  uint32_t cur_ind_gid = 0;

  while (std::fgets(linebuf.data(), (int)linebuf.size(), fp2)) {
    size_t len = std::strlen(linebuf.data());
    while (len > 0 && linebuf[len - 1] != '\n' && !std::feof(fp2)) {
      linebuf.resize(linebuf.size() * 2);
      if (!std::fgets(linebuf.data() + len, (int)(linebuf.size() - len), fp2)) break;
      len += std::strlen(linebuf.data() + len);
    }
    const char* s = linebuf.data();
    p2_lines++;
    if ((p2_lines & 0x7FFFFFFULL) == 0) {
      std::cerr << "  Pass 2: " << (p2_lines >> 20) << "M lines processed...\n";
    }
    if (s[0] != '{' || s[1] != '"') continue;

    // Pass meta, in, il verbatim
    if (std::strncmp(s + 2, "in\":", 4) == 0 ||
        std::strncmp(s + 2, "il\":", 4) == 0 ||
        std::strncmp(s + 2, "meta\":", 6) == 0) {
      std::fwrite(s, 1, len, out_fp);
      out_lines++;
      continue;
    }

    // Expressions
    if (std::strncmp(s + 2, "app\":", 5) == 0) {
      uint32_t ie = 0;
      find_u32(s + 6, "\"ie\":", ie);
      if (!vis_expr[ie]) continue;
      std::string rw = rewrite_u32_keys(std::string_view(s, len), k_app, remap_ie, redirect_name);
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }
    if (std::strncmp(s + 2, "forallE\":", 9) == 0) {
      uint32_t ie = 0;
      find_u32(s + 10, "\"ie\":", ie);
      if (!vis_expr[ie]) continue;
      std::string rw = rewrite_u32_keys(std::string_view(s, len), k_lam_forall, remap_ie, redirect_name);
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }
    if (std::strncmp(s + 2, "const\":", 7) == 0) {
      uint32_t ie = 0;
      find_u32(s + 8, "\"ie\":", ie);
      if (!vis_expr[ie]) continue;
      std::string rw = rewrite_u32_keys(std::string_view(s, len), k_const, remap_ie, redirect_name);
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }
    if (std::strncmp(s + 2, "bvar\":", 6) == 0) {
      uint32_t ie = 0;
      find_u32(s + 7, "\"ie\":", ie);
      if (!vis_expr[ie]) continue;
      std::string rw = rewrite_u32_keys(std::string_view(s, len), k_ie_only, remap_ie, redirect_name);
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }
    if (std::strncmp(s + 2, "ie\":", 4) == 0) {
      uint32_t ie = 0;
      find_u32(s + 1, "\"ie\":", ie);
      if (!vis_expr[ie]) continue;
      std::string rw;
      if (std::strstr(s + 6, "\"lam\":")) {
        rw = rewrite_u32_keys(std::string_view(s, len), k_lam_forall, remap_ie, redirect_name);
      } else if (std::strstr(s + 6, "\"letE\":")) {
        rw = rewrite_u32_keys(std::string_view(s, len), k_let, remap_ie, redirect_name);
      } else if (std::strstr(s + 6, "\"proj\":")) {
        rw = rewrite_u32_keys(std::string_view(s, len), k_proj, remap_ie, redirect_name);
      } else if (std::strstr(s + 6, "\"mdata\":")) {
        rw = rewrite_u32_keys(std::string_view(s, len), k_mdata, remap_ie, redirect_name);
      } else {
        rw = rewrite_u32_keys(std::string_view(s, len), k_ie_only, remap_ie, redirect_name);
      }
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }

    // Declarations
    if (std::strncmp(s + 2, "thm\":", 5) == 0 ||
        std::strncmp(s + 2, "def\":", 5) == 0 ||
        std::strncmp(s + 2, "opaque\":", 8) == 0) {
      uint32_t nm = 0;
      find_u32(s + 5, "\"name\":", nm);
      auto dit = name_to_decl.find(nm);
      if (dit == name_to_decl.end() || !vis_decl[dit->second]) continue;
      std::string rw = rewrite_u32_keys(std::string_view(s, len), k_decl_tv, remap_ie, redirect_name);
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }
    if (std::strncmp(s + 2, "axiom\":", 7) == 0 ||
        std::strncmp(s + 2, "quot\":", 6) == 0) {
      uint32_t nm = 0;
      find_u32(s + 5, "\"name\":", nm);
      auto dit = name_to_decl.find(nm);
      if (dit == name_to_decl.end() || !vis_decl[dit->second]) continue;
      std::string rw = rewrite_u32_keys(std::string_view(s, len), k_decl_t, remap_ie, redirect_name);
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }
    if (std::strncmp(s + 2, "inductive\":", 11) == 0) {
      uint32_t gid = cur_ind_gid++;
      if (!vis_group[gid]) continue;
      std::string rw = rewrite_u32_keys(std::string_view(s, len), k_ind, remap_ie, redirect_name);
      std::fwrite(rw.data(), 1, rw.size(), out_fp);
      out_lines++;
      continue;
    }
  }
  close_stream(fp2);
  std::fclose(out_fp);
  std::cerr << "Done! Wrote " << out_lines << " lines (from " << p2_lines << ").\n";
  return 0;
}
