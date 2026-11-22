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

template <typename T, size_t PAGE_BITS = 22>
struct PagedVec {
  static constexpr size_t PAGE_SIZE = size_t(1) << PAGE_BITS;
  static constexpr size_t PAGE_MASK = PAGE_SIZE - 1;
  std::vector<T*> pages;
  size_t sz = 0;

  ~PagedVec() { clear_and_free(); }
  PagedVec() = default;
  PagedVec(const PagedVec&) = delete;
  PagedVec& operator=(const PagedVec&) = delete;
  PagedVec(PagedVec&& o) noexcept : pages(std::move(o.pages)), sz(o.sz) { o.sz = 0; }
  PagedVec& operator=(PagedVec&& o) noexcept {
    if (this != &o) {
      clear_and_free();
      pages = std::move(o.pages);
      sz = o.sz;
      o.sz = 0;
    }
    return *this;
  }

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

  uint32_t push_back(const T& val) {
    uint32_t idx = (uint32_t)sz;
    ensure(idx);
    (*this)[idx] = val;
    return idx;
  }

  T& operator[](size_t idx) { return pages[idx >> PAGE_BITS][idx & PAGE_MASK]; }
  const T& operator[](size_t idx) const { return pages[idx >> PAGE_BITS][idx & PAGE_MASK]; }
  size_t size() const { return sz; }
};

enum ExprTag : uint8_t {
  ET_BVAR = 1,    // a = bvar_idx
  ET_SORT = 2,    // a = cil
  ET_CONST = 3,   // a = name_id, b = level_list_id
  ET_APP = 4,     // a = fn_cid, b = arg_cid
  ET_FORALL = 5,  // a = ty_cid, b = bd_cid
  ET_LAM = 6,     // a = ty_cid, b = bd_cid
  ET_LET = 7,     // a = ty_cid, b = val_cid, c = bd_cid
  ET_PROJ = 8,    // a = typeName_id, b = proj_idx, c = struct_cid
  ET_LIT = 9      // a = lit_id
};

#pragma pack(push, 1)
struct CExpr {
  uint8_t tag;
  uint32_t a;
  uint32_t b;
  uint32_t c;
  bool operator==(const CExpr& o) const {
    return tag == o.tag && a == o.a && b == o.b && c == o.c;
  }
};  // 13 bytes
#pragma pack(pop)

static inline uint64_t hash_cexpr(const CExpr& e) {
  uint64_t x = ((uint64_t)e.tag << 56) ^ ((uint64_t)e.a << 24) ^ e.b;
  uint64_t y = ((uint64_t)e.c * 0x9e3779b97f4a7c15ULL) ^ x;
  y ^= y >> 30;
  y *= 0xbf58476d1ce4e5b9ULL;
  y ^= y >> 27;
  y *= 0x94d049bb133111ebULL;
  y ^= y >> 31;
  return y;
}

// Key-free open-addressed hash-cons table storing uint32_t CExpr IDs!
struct ExprConsTable {
  std::vector<uint32_t> slots;
  size_t mask = 0;
  size_t count = 0;

  void init(size_t pow2_cap) {
    slots.assign(pow2_cap, 0xFFFFFFFFu);
    mask = pow2_cap - 1;
    count = 0;
  }

  void rehash(size_t new_cap, const PagedVec<CExpr>& nodes) {
    std::vector<uint32_t> old_slots = std::move(slots);
    slots.assign(new_cap, 0xFFFFFFFFu);
    mask = new_cap - 1;
    for (uint32_t id : old_slots) {
      if (id == 0xFFFFFFFFu) continue;
      size_t pos = (size_t)hash_cexpr(nodes[id]) & mask;
      while (slots[pos] != 0xFFFFFFFFu) pos = (pos + 1) & mask;
      slots[pos] = id;
    }
  }

  uint32_t intern(const CExpr& e, PagedVec<CExpr>& nodes, PagedVec<uint8_t>& has_lp, uint8_t lp_flag) {
    if (count * 10 >= slots.size() * 7) {
      std::cerr << "  [ConsTable] Rehashing " << slots.size() << " -> " << (slots.size() * 2) << "...\n";
      rehash(slots.size() * 2, nodes);
    }
    size_t pos = (size_t)hash_cexpr(e) & mask;
    while (true) {
      uint32_t cur = slots[pos];
      if (cur == 0xFFFFFFFFu) {
        uint32_t nid = nodes.push_back(e);
        has_lp.ensure(nid);
        has_lp[nid] = lp_flag;
        slots[pos] = nid;
        count++;
        return nid;
      }
      if (nodes[cur] == e) return cur;
      pos = (pos + 1) & mask;
    }
  }
};

enum LevelTag : uint8_t {
  LT_ZERO = 0,
  LT_SUCC = 1,   // a = cil
  LT_MAX = 2,    // a = cil1, b = cil2
  LT_IMAX = 3,   // a = cil1, b = cil2
  LT_PARAM = 4   // a = name_id
};

struct CLevel {
  uint8_t tag;
  uint32_t a;
  uint32_t b;
  bool operator==(const CLevel& o) const {
    return tag == o.tag && a == o.a && b == o.b;
  }
};

struct CLevelHash {
  size_t operator()(const CLevel& l) const {
    uint64_t h = ((uint64_t)l.tag << 56) ^ ((uint64_t)l.a << 28) ^ l.b;
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccdULL;
    return (size_t)(h ^ (h >> 33));
  }
};

struct VecU32Hash {
  size_t operator()(const std::vector<uint32_t>& v) const {
    uint64_t h = 14695981039346656037ULL;
    for (uint32_t x : v) {
      h ^= x;
      h *= 1099511628211ULL;
    }
    return (size_t)h;
  }
};

struct NameEntry {
  uint32_t pre = 0;
  bool is_num = false;
  uint64_t num_i = 0;
  std::string raw_json_str;  // exact JSON-escaped content WITH surrounding quotes for str, e.g. "\"Eq\""
  std::string decoded_seg;   // decoded UTF-8 segment for protected_names lookup
};

struct DeclRec {
  uint32_t name_id = 0;
  char kind = '?';           // 't','d','o','a','q','c','r','i'
  uint32_t group_id = 0xFFFFFFFFu;
  uint32_t type_cid = 0xFFFFFFFFu;
  uint32_t val_cid = 0xFFFFFFFFu;
  bool single_all = false;
  std::vector<uint32_t> all_names;
  std::vector<uint32_t> level_params;
  std::string extra_sig;     // hints + safety for 'd'
  std::string raw_line;      // non-inductive raw JSON line (with expr IDs rewritten to initial cids!)
};

struct IndGroup {
  std::vector<uint32_t> decl_indices;
  std::vector<uint32_t> all_expr_cids;  // every type & rhs cid in this inductive line
  std::vector<uint32_t> all_name_ids;   // every name, levelParam, ctor, induct, all name_id in this line
  std::string raw_line;                 // inductive raw JSON line (with expr IDs rewritten to initial cids!)
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

static inline bool find_u64(const char* s, const char* key, uint64_t& out) {
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
  out = v;
  return true;
}

static std::vector<uint32_t> parse_u32_array(const char* s, const char* key) {
  std::vector<uint32_t> res;
  const char* p = std::strstr(s, key);
  if (!p) return res;
  p += std::strlen(key);
  if (*p != '[') return res;
  p++;
  while (*p && *p != ']') {
    while (*p == ' ' || *p == ',') p++;
    if (*p >= '0' && *p <= '9') {
      uint64_t v = 0;
      while (*p >= '0' && *p <= '9') {
        v = v * 10 + (*p - '0');
        p++;
      }
      res.push_back((uint32_t)v);
    } else {
      break;
    }
  }
  return res;
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

static std::string decode_json_quoted(std::string_view qstr) {
  std::string out;
  if (qstr.size() < 2 || qstr.front() != '"') return out;
  size_t i = 1, end = qstr.size() - 1;
  while (i < end) {
    if (qstr[i] == '\\' && i + 1 < end) {
      i++;
      switch (qstr[i]) {
        case '"': out.push_back('"'); i++; break;
        case '\\': out.push_back('\\'); i++; break;
        case '/': out.push_back('/'); i++; break;
        case 'n': out.push_back('\n'); i++; break;
        case 'r': out.push_back('\r'); i++; break;
        case 't': out.push_back('\t'); i++; break;
        case 'u': {
          i++;
          unsigned code = 0;
          for (int k = 0; k < 4 && i < end; k++, i++) {
            code <<= 4;
            char c = qstr[i];
            if (c >= '0' && c <= '9') code |= (c - '0');
            else if (c >= 'a' && c <= 'f') code |= (c - 'a' + 10);
            else if (c >= 'A' && c <= 'F') code |= (c - 'A' + 10);
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
        default: out.push_back(qstr[i++]); break;
      }
    } else {
      out.push_back(qstr[i++]);
    }
  }
  return out;
}

// Rewrite all expr keys ("type":, "value":, "rhs":) AND optionally name keys/arrays inside a declaration JSON line!
template <typename MapExprFn, typename MapNameFn>
static std::string rewrite_decl_json(std::string_view line, MapExprFn map_expr, MapNameFn map_name,
                                     bool remap_names, std::vector<uint32_t>* out_exprs = nullptr,
                                     std::vector<uint32_t>* out_names = nullptr) {
  static const std::string_view expr_scalar_keys[] = {"\"type\":", "\"value\":", "\"rhs\":"};
  static const std::string_view name_scalar_keys[] = {"\"name\":", "\"induct\":", "\"ctor\":"};
  static const std::string_view name_array_keys[] = {"\"all\":[", "\"levelParams\":[", "\"ctors\":["};

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
      bool handled = false;
      for (std::string_view k : expr_scalar_keys) {
        if (i + k.size() <= line.size() && line.substr(i, k.size()) == k) {
          size_t j = i + k.size();
          if (j < line.size() && line[j] >= '0' && line[j] <= '9') {
            uint64_t val = 0;
            while (j < line.size() && line[j] >= '0' && line[j] <= '9') val = val * 10 + (line[j++] - '0');
            uint32_t mapped = map_expr((uint32_t)val);
            if (out_exprs) out_exprs->push_back(mapped);
            out.append(k);
            out.append(std::to_string(mapped));
            i = j;
            handled = true;
            break;
          }
        }
      }
      if (handled) continue;

      for (std::string_view k : name_scalar_keys) {
        if (i + k.size() <= line.size() && line.substr(i, k.size()) == k) {
          size_t j = i + k.size();
          if (j < line.size() && line[j] >= '0' && line[j] <= '9') {
            uint64_t val = 0;
            while (j < line.size() && line[j] >= '0' && line[j] <= '9') val = val * 10 + (line[j++] - '0');
            uint32_t orig = (uint32_t)val;
            if (out_names) out_names->push_back(orig);
            uint32_t mapped = remap_names ? map_name(orig) : orig;
            out.append(k);
            out.append(std::to_string(mapped));
            i = j;
            handled = true;
            break;
          }
        }
      }
      if (handled) continue;

      for (std::string_view k : name_array_keys) {
        if (i + k.size() <= line.size() && line.substr(i, k.size()) == k) {
          size_t j = i + k.size();
          // Note: top-level `"ctors":[{...` starts with `{`, whereas `"types":[{...,"ctors":[9]` starts with `0-9` or `]`!
          if (j < line.size() && ((line[j] >= '0' && line[j] <= '9') || line[j] == ']')) {
            out.append(k);
            while (j < line.size() && line[j] != ']') {
              if (line[j] >= '0' && line[j] <= '9') {
                uint64_t val = 0;
                while (j < line.size() && line[j] >= '0' && line[j] <= '9') val = val * 10 + (line[j++] - '0');
                uint32_t orig = (uint32_t)val;
                if (out_names) out_names->push_back(orig);
                uint32_t mapped = remap_names ? map_name(orig) : orig;
                out.append(std::to_string(mapped));
              } else {
                out.push_back(line[j++]);
              }
            }
            if (j < line.size() && line[j] == ']') {
              out.push_back(']');
              j++;
            }
            i = j;
            handled = true;
            break;
          }
        }
      }
      if (handled) continue;

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
    std::cerr << "Usage: rewrite_export_v2 <input.ndjson[.zst]> <challenge_decls.tsv> <output.ndjson>\n";
    return 1;
  }
  std::string in_path = argv[1];
  std::string chal_tsv = argv[2];
  std::string out_path = argv[3];
  bool is_zst = (in_path.size() > 4 && in_path.substr(in_path.size() - 4) == ".zst");

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

  // Core stores
  std::string meta_line = "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"3.1.0\"}}}\n";
  std::vector<NameEntry> names(1);  // 0 = anonymous
  names.reserve(15000000);

  std::vector<CLevel> clevels = {{LT_ZERO, 0, 0}};
  std::vector<uint8_t> cl_has_lp = {0};
  std::unordered_map<CLevel, uint32_t, CLevelHash> level_cons;
  level_cons[{LT_ZERO, 0, 0}] = 0;
  std::vector<uint32_t> raw_to_cil = {0};

  auto intern_level = [&](CLevel lv) -> uint32_t {
    auto it = level_cons.find(lv);
    if (it != level_cons.end()) return it->second;
    uint32_t id = (uint32_t)clevels.size();
    uint8_t lp = 0;
    if (lv.tag == LT_PARAM) lp = 1;
    else if (lv.tag == LT_SUCC) lp = cl_has_lp[lv.a];
    else if (lv.tag == LT_MAX || lv.tag == LT_IMAX) lp = cl_has_lp[lv.a] | cl_has_lp[lv.b];
    clevels.push_back(lv);
    cl_has_lp.push_back(lp);
    level_cons[lv] = id;
    return id;
  };

  std::vector<std::vector<uint32_t>> level_lists = {{}};
  std::vector<uint8_t> ll_has_lp = {0};
  std::unordered_map<std::vector<uint32_t>, uint32_t, VecU32Hash> ll_cons;
  ll_cons[{}] = 0;
  auto intern_ll = [&](std::vector<uint32_t>&& v) -> uint32_t {
    auto it = ll_cons.find(v);
    if (it != ll_cons.end()) return it->second;
    uint32_t id = (uint32_t)level_lists.size();
    uint8_t lp = 0;
    for (uint32_t c : v) lp |= cl_has_lp[c];
    ll_cons[v] = id;
    level_lists.push_back(std::move(v));
    ll_has_lp.push_back(lp);
    return id;
  };

  std::vector<std::string> literals;  // e.g. "\"natVal\":\"0\"" or "\"strVal\":\"Lean\""
  std::unordered_map<std::string, uint32_t> lit_cons;
  auto intern_lit = [&](std::string&& s) -> uint32_t {
    auto it = lit_cons.find(s);
    if (it != lit_cons.end()) return it->second;
    uint32_t id = (uint32_t)literals.size();
    lit_cons[s] = id;
    literals.push_back(std::move(s));
    return id;
  };

  PagedVec<CExpr> cnodes;
  PagedVec<uint8_t> cnode_has_lp;
  ExprConsTable econs;
  // Pre-size to 2^31 (8 GiB) for multi-GB solution streams to avoid any rehashing!
  bool large_input = false;
  if (!is_zst) {
    FILE* tf = std::fopen(in_path.c_str(), "rb");
    if (tf) {
      std::fseek(tf, 0, SEEK_END);
      if (std::ftell(tf) > (1LL << 30)) large_input = true;
      std::fclose(tf);
    }
  } else {
    large_input = true;
  }
  econs.init(large_input ? (size_t(1) << 31) : (size_t(1) << 20));

  PagedVec<uint32_t> raw_to_cid;
  std::vector<DeclRec> decls;
  std::vector<IndGroup> ind_groups;
  std::unordered_map<uint32_t, uint32_t> name_to_decl;
  decls.reserve(1500000);
  name_to_decl.reserve(1500000);

  // ===================== SINGLE STREAM READ PASS =====================
  std::cerr << "=== Streaming & Alpha/Binder/MData Hash-Consing " << in_path << " ===\n";
  FILE* fp = is_zst ? popen(("zstd -dc --long=30 \"" + in_path + "\"").c_str(), "r")
                    : std::fopen(in_path.c_str(), "rb");
  if (!fp) { std::perror("open input"); return 1; }
  std::vector<char> inbuf(8 * 1024 * 1024);
  if (!is_zst) std::setvbuf(fp, inbuf.data(), _IOFBF, inbuf.size());

  std::vector<char> linebuf(16 * 1024 * 1024);
  uint64_t line_cnt = 0, raw_expr_lines = 0, mdata_stripped = 0;

  while (std::fgets(linebuf.data(), (int)linebuf.size(), fp)) {
    size_t len = std::strlen(linebuf.data());
    while (len > 0 && linebuf[len - 1] != '\n' && !std::feof(fp)) {
      linebuf.resize(linebuf.size() * 2);
      if (!std::fgets(linebuf.data() + len, (int)(linebuf.size() - len), fp)) break;
      len += std::strlen(linebuf.data() + len);
    }
    const char* s = linebuf.data();
    line_cnt++;
    if ((line_cnt & 0x7FFFFFFULL) == 0) {
      std::cerr << "  Read " << (line_cnt >> 20) << "M lines | raw_exprs=" << raw_expr_lines
                << " -> unique_cnodes=" << cnodes.size()
                << " (-" << (100.0 * (raw_expr_lines - cnodes.size()) / std::max<uint64_t>(1, raw_expr_lines)) << "%)\n";
    }
    if (s[0] != '{' || s[1] != '"') continue;

    if (std::strncmp(s + 2, "meta\":", 6) == 0) {
      meta_line.assign(s, len);
      continue;
    }

    if (std::strncmp(s + 2, "in\":", 4) == 0) {
      uint32_t id = 0, pre = 0;
      find_u32(s + 1, "\"in\":", id);
      find_u32(s + 5, "\"pre\":", pre);
      if (id >= names.size()) names.resize(id + 1);
      const char* sp = std::strstr(s + 6, "\"str\":{\"pre\":");
      if (sp) {
        std::string qstr = extract_bracket_slice(sp + 13, "\"str\":");
        std::string dec = decode_json_quoted(qstr);
        names[id] = {pre, false, 0, std::move(qstr), std::move(dec)};
      } else {
        uint64_t num_i = 0;
        find_u64(s + 5, "\"i\":", num_i);
        names[id] = {pre, true, num_i, "", std::to_string(num_i)};
      }
      continue;
    }

    if (std::strncmp(s + 2, "il\":", 4) == 0) {
      uint32_t il = 0;
      find_u32(s + 1, "\"il\":", il);
      if (il >= raw_to_cil.size()) raw_to_cil.resize(il + 1, 0);
      uint32_t v = 0;
      if (find_u32(s + 5, "\"param\":", v)) {
        raw_to_cil[il] = intern_level({LT_PARAM, v, 0});
      } else if (find_u32(s + 5, "\"succ\":", v)) {
        raw_to_cil[il] = intern_level({LT_SUCC, raw_to_cil[v], 0});
      } else if (std::strstr(s + 5, "\"max\":[")) {
        auto arr = parse_u32_array(s + 5, "\"max\":");
        if (arr.size() == 2) raw_to_cil[il] = intern_level({LT_MAX, raw_to_cil[arr[0]], raw_to_cil[arr[1]]});
      } else if (std::strstr(s + 5, "\"imax\":[")) {
        auto arr = parse_u32_array(s + 5, "\"imax\":");
        if (arr.size() == 2) raw_to_cil[il] = intern_level({LT_IMAX, raw_to_cil[arr[0]], raw_to_cil[arr[1]]});
      }
      continue;
    }

    // Expressions!
    if (std::strncmp(s + 2, "app\":", 5) == 0) {
      raw_expr_lines++;
      uint32_t arg = 0, fn = 0, ie = 0;
      find_u32(s + 6, "\"arg\":", arg);
      find_u32(s + 6, "\"fn\":", fn);
      find_u32(s + 6, "\"ie\":", ie);
      uint32_t cfn = raw_to_cid[fn], carg = raw_to_cid[arg];
      raw_to_cid.ensure(ie);
      raw_to_cid[ie] = econs.intern({ET_APP, cfn, carg, 0}, cnodes, cnode_has_lp, cnode_has_lp[cfn] | cnode_has_lp[carg]);
      continue;
    }
    if (std::strncmp(s + 2, "forallE\":", 9) == 0) {
      raw_expr_lines++;
      uint32_t body = 0, type = 0, ie = 0;
      find_u32(s + 10, "\"body\":", body);
      find_u32(s + 10, "\"type\":", type);
      find_u32(s + 10, "\"ie\":", ie);
      uint32_t cty = raw_to_cid[type], cbd = raw_to_cid[body];
      raw_to_cid.ensure(ie);
      raw_to_cid[ie] = econs.intern({ET_FORALL, cty, cbd, 0}, cnodes, cnode_has_lp, cnode_has_lp[cty] | cnode_has_lp[cbd]);
      continue;
    }
    if (std::strncmp(s + 2, "const\":", 7) == 0) {
      raw_expr_lines++;
      uint32_t nm = 0, ie = 0;
      find_u32(s + 8, "\"name\":", nm);
      find_u32(s + 8, "\"ie\":", ie);
      auto raw_us = parse_u32_array(s + 8, "\"us\":");
      for (uint32_t& u : raw_us) u = raw_to_cil[u];
      uint32_t ll_id = intern_ll(std::move(raw_us));
      raw_to_cid.ensure(ie);
      raw_to_cid[ie] = econs.intern({ET_CONST, nm, ll_id, 0}, cnodes, cnode_has_lp, ll_has_lp[ll_id]);
      continue;
    }
    if (std::strncmp(s + 2, "bvar\":", 6) == 0) {
      raw_expr_lines++;
      uint32_t bv = 0, ie = 0;
      find_u32(s + 1, "\"bvar\":", bv);
      find_u32(s + 7, "\"ie\":", ie);
      raw_to_cid.ensure(ie);
      raw_to_cid[ie] = econs.intern({ET_BVAR, bv, 0, 0}, cnodes, cnode_has_lp, 0);
      continue;
    }
    if (std::strncmp(s + 2, "ie\":", 4) == 0) {
      raw_expr_lines++;
      uint32_t ie = 0;
      find_u32(s + 1, "\"ie\":", ie);
      raw_to_cid.ensure(ie);
      if (const char* p = std::strstr(s + 6, "\"sort\":")) {
        uint32_t u = 0;
        find_u32(p, "\"sort\":", u);
        uint32_t cu = raw_to_cil[u];
        raw_to_cid[ie] = econs.intern({ET_SORT, cu, 0, 0}, cnodes, cnode_has_lp, cl_has_lp[cu]);
      } else if (const char* p = std::strstr(s + 6, "\"lam\":")) {
        uint32_t body = 0, type = 0;
        find_u32(p, "\"body\":", body);
        find_u32(p, "\"type\":", type);
        uint32_t cty = raw_to_cid[type], cbd = raw_to_cid[body];
        raw_to_cid[ie] = econs.intern({ET_LAM, cty, cbd, 0}, cnodes, cnode_has_lp, cnode_has_lp[cty] | cnode_has_lp[cbd]);
      } else if (const char* p = std::strstr(s + 6, "\"letE\":")) {
        uint32_t body = 0, type = 0, val = 0;
        find_u32(p, "\"body\":", body);
        find_u32(p, "\"type\":", type);
        find_u32(p, "\"value\":", val);
        uint32_t cty = raw_to_cid[type], cvl = raw_to_cid[val], cbd = raw_to_cid[body];
        raw_to_cid[ie] = econs.intern({ET_LET, cty, cvl, cbd}, cnodes, cnode_has_lp,
                                      cnode_has_lp[cty] | cnode_has_lp[cvl] | cnode_has_lp[cbd]);
      } else if (const char* p = std::strstr(s + 6, "\"proj\":")) {
        uint32_t idx = 0, st = 0, tn = 0;
        find_u32(p, "\"idx\":", idx);
        find_u32(p, "\"struct\":", st);
        find_u32(p, "\"typeName\":", tn);
        uint32_t cst = raw_to_cid[st];
        raw_to_cid[ie] = econs.intern({ET_PROJ, tn, idx, cst}, cnodes, cnode_has_lp, cnode_has_lp[cst]);
      } else if (const char* p = std::strstr(s + 6, "\"mdata\":")) {
        uint32_t ex = 0;
        find_u32(p, "\"expr\":", ex);
        raw_to_cid[ie] = raw_to_cid[ex];
        mdata_stripped++;
      } else if (const char* p = std::strstr(s + 6, "\"natVal\":")) {
        std::string payload = "\"natVal\":" + extract_bracket_slice(p, "\"natVal\":");
        uint32_t lid = intern_lit(std::move(payload));
        raw_to_cid[ie] = econs.intern({ET_LIT, lid, 0, 0}, cnodes, cnode_has_lp, 0);
      } else if (const char* p = std::strstr(s + 6, "\"strVal\":")) {
        std::string payload = "\"strVal\":" + extract_bracket_slice(p, "\"strVal\":");
        uint32_t lid = intern_lit(std::move(payload));
        raw_to_cid[ie] = econs.intern({ET_LIT, lid, 0, 0}, cnodes, cnode_has_lp, 0);
      }
      continue;
    }

    // Declarations: immediately translate raw ie -> cid inside raw_line!
    auto map_raw_ie = [&](uint32_t old_ie) -> uint32_t { return raw_to_cid[old_ie]; };
    auto id_name = [&](uint32_t n) -> uint32_t { return n; };

    if (std::strncmp(s + 2, "thm\":", 5) == 0 ||
        std::strncmp(s + 2, "def\":", 5) == 0 ||
        std::strncmp(s + 2, "opaque\":", 8) == 0) {
      char k = s[2];
      uint32_t nm = 0, tp = 0, vl = 0;
      find_u32(s + 5, "\"name\":", nm);
      find_u32(s + 5, "\"type\":", tp);
      find_u32(s + 5, "\"value\":", vl);
      auto alls = parse_u32_array(s + 5, "\"all\":");
      bool single_all = (alls.size() == 1 && alls[0] == nm);
      auto lps = parse_u32_array(s + 5, "\"levelParams\":");
      std::string extra;
      if (k == 'd') {
        extra = extract_bracket_slice(s + 5, "\"hints\":") + "|" + extract_bracket_slice(s + 5, "\"safety\":");
      }
      std::string rw = rewrite_decl_json(std::string_view(s, len), map_raw_ie, id_name, false);
      uint32_t did = (uint32_t)decls.size();
      decls.push_back({nm, k, 0xFFFFFFFFu, raw_to_cid[tp], raw_to_cid[vl], single_all, std::move(alls), std::move(lps), std::move(extra), std::move(rw)});
      name_to_decl[nm] = did;
      continue;
    }
    if (std::strncmp(s + 2, "axiom\":", 7) == 0 ||
        std::strncmp(s + 2, "quot\":", 6) == 0) {
      char k = s[2];
      uint32_t nm = 0, tp = 0;
      find_u32(s + 5, "\"name\":", nm);
      find_u32(s + 5, "\"type\":", tp);
      auto lps = parse_u32_array(s + 5, "\"levelParams\":");
      std::string rw = rewrite_decl_json(std::string_view(s, len), map_raw_ie, id_name, false);
      uint32_t did = (uint32_t)decls.size();
      decls.push_back({nm, k, 0xFFFFFFFFu, raw_to_cid[tp], 0xFFFFFFFFu, true, {}, std::move(lps), "", std::move(rw)});
      name_to_decl[nm] = did;
      continue;
    }
    if (std::strncmp(s + 2, "inductive\":", 11) == 0) {
      uint32_t gid = (uint32_t)ind_groups.size();
      ind_groups.emplace_back();
      IndGroup& g = ind_groups.back();
      const char* p_ctors = std::strstr(s, "\"ctors\":[");
      const char* p_recs = std::strstr(s, "\"recs\":[");
      const char* p_types = std::strstr(s, "\"types\":[");
      const char* end_line = s + len;
      auto scan_range = [&](const char* beg, const char* end, char kind) {
        if (!beg || !end || beg >= end) return;
        const char* cur = beg;
        while (cur < end) {
          const char* nm_p = std::strstr(cur, "\"name\":");
          if (!nm_p || nm_p >= end) break;
          uint32_t nid = 0, tie = 0;
          if (find_u32(nm_p, "\"name\":", nid) && find_u32(nm_p, "\"type\":", tie)) {
            uint32_t did = (uint32_t)decls.size();
            decls.push_back({nid, kind, gid, raw_to_cid[tie], 0xFFFFFFFFu, false, {}, {}, "", ""});
            name_to_decl[nid] = did;
            g.decl_indices.push_back(did);
          }
          cur = nm_p + 7;
        }
      };
      scan_range(p_ctors, p_recs ? p_recs : end_line, 'c');
      scan_range(p_recs, p_types ? p_types : end_line, 'r');
      scan_range(p_types, end_line, 'i');
      g.raw_line = rewrite_decl_json(std::string_view(s, len), map_raw_ie, id_name, false, &g.all_expr_cids, &g.all_name_ids);
      continue;
    }
  }
  if (is_zst) pclose(fp);
  else std::fclose(fp);

  // Free raw_to_cid + raw_to_cil immediately!
  raw_to_cid.clear_and_free();
  std::vector<uint32_t>().swap(raw_to_cil);

  std::cerr << "Pass 1 Complete:\n"
            << "  Raw expr records:   " << raw_expr_lines << " (mdata stripped: " << mdata_stripped << ")\n"
            << "  Alpha/BI-consed:    " << cnodes.size()
            << " (-" << (raw_expr_lines - cnodes.size()) << ", -"
            << (100.0 * (raw_expr_lines - cnodes.size()) / std::max<uint64_t>(1, raw_expr_lines)) << "% BEFORE GC!)\n"
            << "  Unique levels:      " << clevels.size() << "\n"
            << "  Declarations:       " << decls.size() << "\n";

  // Identify protected declarations & roots
  auto get_full_name = [&](uint32_t nid) -> std::string {
    std::vector<const std::string*> segs;
    uint32_t cur = nid;
    while (cur != 0 && cur < names.size()) {
      segs.push_back(&names[cur].decoded_seg);
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
        fn == "Nat.div" || fn == "Nat.mod" ||
        fn.compare(0, 8, "Nat.div.") == 0 || fn.compare(0, 8, "Nat.mod.") == 0 ||
        fn == "String.mk" || fn == "String.mk._proof_1") {
      root_dids.push_back((uint32_t)i);
    }
  }
  for (auto& ne : names) std::string().swap(ne.decoded_seg);

  // Reserve 32 dummy canonical levelParam name IDs for universe-polymorphic alpha-CSE!
  uint32_t real_names_end = (uint32_t)names.size();
  std::vector<uint32_t> std_lp_cils(32);
  for (int j = 0; j < 32; j++) {
    uint32_t dummy_nid = (uint32_t)names.size();
    names.push_back({0, false, 0, "\"__lp\"", ""});
    std_lp_cils[j] = intern_level({LT_PARAM, dummy_nid, 0});
  }

  auto subst_level_lps = [&](uint32_t cil, const std::vector<uint32_t>& lps, auto& self) -> uint32_t {
    if (!cl_has_lp[cil]) return cil;
    CLevel lv = clevels[cil];
    if (lv.tag == LT_PARAM) {
      for (size_t j = 0; j < lps.size() && j < 32; j++) {
        if (lv.a == lps[j]) return std_lp_cils[j];
      }
      return cil;
    }
    if (lv.tag == LT_SUCC) return intern_level({LT_SUCC, self(lv.a, lps, self), 0});
    return intern_level({lv.tag, self(lv.a, lps, self), self(lv.b, lps, self)});
  };

  auto subst_expr_lps = [&](uint32_t root_cid, const std::vector<uint32_t>& lps) -> uint32_t {
    if (lps.empty() || !cnode_has_lp[root_cid]) return root_cid;
    std::unordered_map<uint32_t, uint32_t> memo;
    auto go = [&](uint32_t cid, auto& self) -> uint32_t {
      if (!cnode_has_lp[cid]) return cid;
      auto mit = memo.find(cid);
      if (mit != memo.end()) return mit->second;
      CExpr e = cnodes[cid];
      uint32_t res = cid;
      switch (e.tag) {
        case ET_SORT: {
          uint32_t nl = subst_level_lps(e.a, lps, subst_level_lps);
          res = econs.intern({ET_SORT, nl, 0, 0}, cnodes, cnode_has_lp, cl_has_lp[nl]);
          break;
        }
        case ET_CONST: {
          std::vector<uint32_t> nus = level_lists[e.b];
          for (uint32_t& u : nus) u = subst_level_lps(u, lps, subst_level_lps);
          uint32_t nll = intern_ll(std::move(nus));
          res = econs.intern({ET_CONST, e.a, nll, 0}, cnodes, cnode_has_lp, ll_has_lp[nll]);
          break;
        }
        case ET_APP:
        case ET_FORALL:
        case ET_LAM: {
          uint32_t na = self(e.a, self), nb = self(e.b, self);
          res = econs.intern({e.tag, na, nb, 0}, cnodes, cnode_has_lp, cnode_has_lp[na] | cnode_has_lp[nb]);
          break;
        }
        case ET_LET: {
          uint32_t na = self(e.a, self), nb = self(e.b, self), nc = self(e.c, self);
          res = econs.intern({ET_LET, na, nb, nc}, cnodes, cnode_has_lp,
                             cnode_has_lp[na] | cnode_has_lp[nb] | cnode_has_lp[nc]);
          break;
        }
        case ET_PROJ: {
          uint32_t nc = self(e.c, self);
          res = econs.intern({ET_PROJ, e.a, e.b, nc}, cnodes, cnode_has_lp, cnode_has_lp[nc]);
          break;
        }
        default: break;
      }
      memo[cid] = res;
      return res;
    };
    return go(root_cid, go);
  };

  // ===================== ITERATED DEF + PROP CSE + DAG RE-CANONICALIZATION =====================
  std::unordered_map<uint32_t, uint32_t> redirect_name;
  auto resolve_name = [&](uint32_t nm) -> uint32_t {
    auto it = redirect_name.find(nm);
    while (it != redirect_name.end()) {
      nm = it->second;
      it = redirect_name.find(nm);
    }
    return nm;
  };

  for (int round = 1; round <= 3; round++) {
    std::unordered_map<std::string, uint32_t> first_thm, first_def;
    size_t new_thm_redirs = 0, new_def_redirs = 0;

    for (size_t i = 0; i < decls.size(); i++) {
      const DeclRec& d = decls[i];
      if (!d.single_all) continue;
      if (redirect_name.count(d.name_id)) continue;  // already redirected in an earlier round!

      if (d.kind == 't') {
        uint32_t std_ty = subst_expr_lps(d.type_cid, d.level_params);
        std::string key = std::to_string(d.level_params.size()) + "|" + std::to_string(std_ty);
        auto [it, ins] = first_thm.emplace(std::move(key), d.name_id);
        if (!ins && !is_protected[i]) {
          redirect_name[d.name_id] = resolve_name(it->second);
          new_thm_redirs++;
        }
      } else if (d.kind == 'd') {
        // Skip huge defs for LP-subst memo safety if > 50k nodes? Def statements/values are tiny, fast!
        uint32_t std_ty = subst_expr_lps(d.type_cid, d.level_params);
        uint32_t std_vl = subst_expr_lps(d.val_cid, d.level_params);
        std::string key = std::to_string(d.level_params.size()) + "|" + std::to_string(std_ty) + "|" +
                          std::to_string(std_vl) + "|" + d.extra_sig;
        auto [it, ins] = first_def.emplace(std::move(key), d.name_id);
        if (!ins && !is_protected[i]) {
          redirect_name[d.name_id] = resolve_name(it->second);
          new_def_redirs++;
        }
      }
    }

    std::cerr << "  [CSE Round " << round << "] +" << new_thm_redirs << " thm redirects, +"
              << new_def_redirs << " def redirects (total redirected=" << redirect_name.size() << ")\n";
    if (new_thm_redirs == 0 && new_def_redirs == 0) break;

    // Re-canonicalize all real cnodes [0 .. N) bottom-up applying `resolve_name` on ET_CONST!
    // Free old hash table slots BEFORE allocating next_cons to save 8 GiB peak RAM!
    std::vector<uint32_t>().swap(econs.slots);

    size_t old_n = cnodes.size();
    PagedVec<CExpr> next_nodes;
    PagedVec<uint8_t> next_lp;
    ExprConsTable next_cons;
    size_t init_cap = size_t(1) << 20;
    while (init_cap * 7 < old_n * 10) init_cap <<= 1;
    next_cons.init(init_cap);

    PagedVec<uint32_t> cid_map;
    if (old_n > 0) cid_map.ensure(old_n - 1);

    for (size_t c = 0; c < old_n; c++) {
      CExpr e = cnodes[c];
      uint8_t lp = 0;
      switch (e.tag) {
        case ET_BVAR:
        case ET_LIT:
          break;
        case ET_SORT:
          lp = cl_has_lp[e.a];
          break;
        case ET_CONST:
          e.a = resolve_name(e.a);
          lp = ll_has_lp[e.b];
          break;
        case ET_APP:
        case ET_FORALL:
        case ET_LAM:
          e.a = cid_map[e.a];
          e.b = cid_map[e.b];
          lp = next_lp[e.a] | next_lp[e.b];
          break;
        case ET_LET:
          e.a = cid_map[e.a];
          e.b = cid_map[e.b];
          e.c = cid_map[e.c];
          lp = next_lp[e.a] | next_lp[e.b] | next_lp[e.c];
          break;
        case ET_PROJ:
          e.c = cid_map[e.c];
          lp = next_lp[e.c];
          break;
      }
      cid_map[c] = next_cons.intern(e, next_nodes, next_lp, lp);
    }

    auto map_c = [&](uint32_t old_c) -> uint32_t { return cid_map[old_c]; };
    auto id_nm = [&](uint32_t n) -> uint32_t { return n; };

    for (auto& d : decls) {
      if (d.type_cid != 0xFFFFFFFFu) d.type_cid = cid_map[d.type_cid];
      if (d.val_cid != 0xFFFFFFFFu) d.val_cid = cid_map[d.val_cid];
      if (!d.raw_line.empty()) {
        d.raw_line = rewrite_decl_json(d.raw_line, map_c, id_nm, false);
      }
    }
    for (auto& g : ind_groups) {
      g.all_expr_cids.clear();
      g.raw_line = rewrite_decl_json(g.raw_line, map_c, id_nm, false, &g.all_expr_cids, nullptr);
    }

    cnodes = std::move(next_nodes);
    cnode_has_lp = std::move(next_lp);
    econs = std::move(next_cons);
    std::cerr << "  [After Round " << round << " Re-Hash-Cons] Unique cnodes: " << old_n << " -> " << cnodes.size() << "\n";
  }

  // Free hash-cons table slots before GC!
  std::vector<uint32_t>().swap(econs.slots);

  // ===================== BIPARTITE GC (Decls + Exprs + Levels + Names) =====================
  std::vector<uint8_t> vis_decl(decls.size(), 0);
  std::vector<uint8_t> vis_group(ind_groups.size(), 0);
  PagedVec<uint8_t> vis_cid;
  if (cnodes.size() > 0) vis_cid.ensure(cnodes.size() - 1);
  std::vector<uint8_t> vis_cil(clevels.size(), 0);
  vis_cil[0] = 1;  // 0 = Level.zero built-in
  std::vector<uint8_t> vis_name(real_names_end, 0);
  vis_name[0] = 1; // 0 = Name.anonymous built-in

  auto mark_name = [&](uint32_t nid) {
    while (nid != 0 && nid < real_names_end && !vis_name[nid]) {
      vis_name[nid] = 1;
      nid = names[nid].pre;
    }
  };
  auto mark_level = [&](uint32_t cil, auto& self) -> void {
    if (cil >= clevels.size() || vis_cil[cil]) return;
    vis_cil[cil] = 1;
    const CLevel& lv = clevels[cil];
    if (lv.tag == LT_PARAM) mark_name(lv.a);
    else if (lv.tag == LT_SUCC) self(lv.a, self);
    else if (lv.tag == LT_MAX || lv.tag == LT_IMAX) { self(lv.a, self); self(lv.b, self); }
  };

  std::vector<uint32_t> q_decl, q_cid;
  auto push_decl = [&](uint32_t did) {
    if (did < decls.size() && !vis_decl[did]) {
      vis_decl[did] = 1;
      q_decl.push_back(did);
    }
  };
  auto push_cid = [&](uint32_t cid) {
    if (cid != 0xFFFFFFFFu && cid < cnodes.size() && !vis_cid[cid]) {
      vis_cid[cid] = 1;
      q_cid.push_back(cid);
    }
  };

  for (uint32_t r : root_dids) push_decl(r);

  while (!q_decl.empty() || !q_cid.empty()) {
    while (!q_decl.empty()) {
      uint32_t did = q_decl.back();
      q_decl.pop_back();
      const DeclRec& d = decls[did];
      mark_name(d.name_id);
      for (uint32_t an : d.all_names) {
        mark_name(an);
        auto dit = name_to_decl.find(an);
        if (dit != name_to_decl.end()) push_decl(dit->second);
      }
      for (uint32_t lp : d.level_params) mark_name(lp);
      push_cid(d.type_cid);
      push_cid(d.val_cid);
      if (d.group_id != 0xFFFFFFFFu && !vis_group[d.group_id]) {
        vis_group[d.group_id] = 1;
        for (uint32_t m : ind_groups[d.group_id].decl_indices) push_decl(m);
        for (uint32_t ex : ind_groups[d.group_id].all_expr_cids) push_cid(ex);
        for (uint32_t nm : ind_groups[d.group_id].all_name_ids) mark_name(nm);
      }
    }
    while (!q_cid.empty()) {
      uint32_t cid = q_cid.back();
      q_cid.pop_back();
      const CExpr& e = cnodes[cid];
      switch (e.tag) {
        case ET_SORT:
          mark_level(e.a, mark_level);
          break;
        case ET_CONST: {
          uint32_t nm = resolve_name(e.a);
          mark_name(nm);
          for (uint32_t u : level_lists[e.b]) mark_level(u, mark_level);
          auto dit = name_to_decl.find(nm);
          if (dit != name_to_decl.end()) push_decl(dit->second);
          break;
        }
        case ET_APP:
        case ET_FORALL:
        case ET_LAM:
          push_cid(e.a);
          push_cid(e.b);
          break;
        case ET_LET:
          push_cid(e.a);
          push_cid(e.b);
          push_cid(e.c);
          break;
        case ET_PROJ: {
          mark_name(e.a);
          push_cid(e.c);
          auto dit = name_to_decl.find(e.a);
          if (dit != name_to_decl.end()) push_decl(dit->second);
          break;
        }
        default: break;
      }
    }
  }

  // Dense topological remaps: names (1..N'), levels (1..L'), exprs (0..E'-1)
  std::vector<uint32_t> remap_in(real_names_end, 0);
  uint32_t out_in_cnt = 0;
  for (uint32_t i = 1; i < real_names_end; i++) {
    if (vis_name[i]) remap_in[i] = ++out_in_cnt;
  }

  std::vector<uint32_t> remap_il(clevels.size(), 0);
  uint32_t out_il_cnt = 0;
  for (uint32_t i = 1; i < clevels.size(); i++) {
    if (vis_cil[i]) remap_il[i] = ++out_il_cnt;
  }

  PagedVec<uint32_t> remap_cid;
  if (cnodes.size() > 0) remap_cid.ensure(cnodes.size() - 1);
  uint32_t out_ie_cnt = 0;
  for (size_t c = 0; c < cnodes.size(); c++) {
    if (vis_cid[c]) remap_cid[c] = out_ie_cnt++;
  }

  size_t out_decl_cnt = 0;
  for (uint8_t v : vis_decl) out_decl_cnt += v;

  std::cerr << "=== FINAL V2 SKINNY KERNEL SUMMARY ===\n"
            << "  Names (in):        " << (real_names_end - 1) << " -> " << out_in_cnt << "\n"
            << "  Levels (il):       " << (clevels.size() - 1) << " -> " << out_il_cnt << "\n"
            << "  Expressions (ie):  " << raw_expr_lines << " -> " << out_ie_cnt
            << " (-" << (100.0 * (raw_expr_lines - out_ie_cnt) / std::max<uint64_t>(1, raw_expr_lines)) << "%!)\n"
            << "  Declarations:      " << decls.size() << " -> " << out_decl_cnt << "\n";

  // ===================== SYNTHESIZE COMPACT NDJSON DIRECTLY FROM RAM =====================
  std::cerr << "=== Emitting " << out_path << " ===\n";
  FILE* out_fp = std::fopen(out_path.c_str(), "wb");
  if (!out_fp) { std::perror("open output"); return 1; }
  std::vector<char> outbuf(16 * 1024 * 1024);
  std::setvbuf(out_fp, outbuf.data(), _IOFBF, outbuf.size());

  std::fwrite(meta_line.data(), 1, meta_line.size(), out_fp);

  std::string line;
  line.reserve(4096);

  // 1. Names (`1 .. out_in_cnt`)
  for (uint32_t i = 1; i < real_names_end; i++) {
    if (!vis_name[i]) continue;
    line.clear();
    line += "{\"in\":";
    line += std::to_string(remap_in[i]);
    if (names[i].is_num) {
      line += ",\"num\":{\"i\":";
      line += std::to_string(names[i].num_i);
      line += ",\"pre\":";
      line += std::to_string(remap_in[names[i].pre]);
      line += "}}\n";
    } else {
      line += ",\"str\":{\"pre\":";
      line += std::to_string(remap_in[names[i].pre]);
      line += ",\"str\":";
      line += names[i].raw_json_str;
      line += "}}\n";
    }
    std::fwrite(line.data(), 1, line.size(), out_fp);
  }

  // 2. Levels (`1 .. out_il_cnt`)
  for (uint32_t i = 1; i < clevels.size(); i++) {
    if (!vis_cil[i]) continue;
    line.clear();
    line += "{\"il\":";
    line += std::to_string(remap_il[i]);
    const CLevel& lv = clevels[i];
    if (lv.tag == LT_PARAM) {
      line += ",\"param\":";
      line += std::to_string(remap_in[lv.a]);
    } else if (lv.tag == LT_SUCC) {
      line += ",\"succ\":";
      line += std::to_string(remap_il[lv.a]);
    } else if (lv.tag == LT_MAX) {
      line += ",\"max\":[";
      line += std::to_string(remap_il[lv.a]);
      line += ",";
      line += std::to_string(remap_il[lv.b]);
      line += "]";
    } else if (lv.tag == LT_IMAX) {
      line += ",\"imax\":[";
      line += std::to_string(remap_il[lv.a]);
      line += ",";
      line += std::to_string(remap_il[lv.b]);
      line += "]";
    }
    line += "}\n";
    std::fwrite(line.data(), 1, line.size(), out_fp);
  }

  // 3. Expressions (`0 .. out_ie_cnt - 1`)
  for (size_t c = 0; c < cnodes.size(); c++) {
    if (!vis_cid[c]) continue;
    uint32_t nid = remap_cid[c];
    const CExpr& e = cnodes[c];
    line.clear();
    switch (e.tag) {
      case ET_BVAR:
        line += "{\"bvar\":";
        line += std::to_string(e.a);
        line += ",\"ie\":";
        line += std::to_string(nid);
        line += "}\n";
        break;
      case ET_SORT:
        line += "{\"ie\":";
        line += std::to_string(nid);
        line += ",\"sort\":";
        line += std::to_string(remap_il[e.a]);
        line += "}\n";
        break;
      case ET_CONST: {
        uint32_t nm = remap_in[resolve_name(e.a)];
        line += "{\"const\":{\"name\":";
        line += std::to_string(nm);
        line += ",\"us\":[";
        const auto& us = level_lists[e.b];
        for (size_t j = 0; j < us.size(); j++) {
          if (j) line.push_back(',');
          line += std::to_string(remap_il[us[j]]);
        }
        line += "]},\"ie\":";
        line += std::to_string(nid);
        line += "}\n";
        break;
      }
      case ET_APP:
        line += "{\"app\":{\"arg\":";
        line += std::to_string(remap_cid[e.b]);
        line += ",\"fn\":";
        line += std::to_string(remap_cid[e.a]);
        line += "},\"ie\":";
        line += std::to_string(nid);
        line += "}\n";
        break;
      case ET_FORALL:
        line += "{\"forallE\":{\"binderInfo\":\"default\",\"body\":";
        line += std::to_string(remap_cid[e.b]);
        line += ",\"name\":0,\"type\":";
        line += std::to_string(remap_cid[e.a]);
        line += "},\"ie\":";
        line += std::to_string(nid);
        line += "}\n";
        break;
      case ET_LAM:
        line += "{\"ie\":";
        line += std::to_string(nid);
        line += ",\"lam\":{\"binderInfo\":\"default\",\"body\":";
        line += std::to_string(remap_cid[e.b]);
        line += ",\"name\":0,\"type\":";
        line += std::to_string(remap_cid[e.a]);
        line += "}}\n";
        break;
      case ET_LET:
        line += "{\"ie\":";
        line += std::to_string(nid);
        line += ",\"letE\":{\"body\":";
        line += std::to_string(remap_cid[e.c]);
        line += ",\"name\":0,\"nondep\":false,\"type\":";
        line += std::to_string(remap_cid[e.a]);
        line += ",\"value\":";
        line += std::to_string(remap_cid[e.b]);
        line += "}}\n";
        break;
      case ET_PROJ:
        line += "{\"ie\":";
        line += std::to_string(nid);
        line += ",\"proj\":{\"idx\":";
        line += std::to_string(e.b);
        line += ",\"struct\":";
        line += std::to_string(remap_cid[e.c]);
        line += ",\"typeName\":";
        line += std::to_string(remap_in[e.a]);
        line += "}}\n";
        break;
      case ET_LIT:
        line += "{\"ie\":";
        line += std::to_string(nid);
        line.push_back(',');
        line += literals[e.a];
        line += "}\n";
        break;
    }
    std::fwrite(line.data(), 1, line.size(), out_fp);
  }

  // 4. Declarations (in exact original stream order!)
  auto map_final_cid = [&](uint32_t cid) -> uint32_t { return remap_cid[cid]; };
  auto map_final_in = [&](uint32_t nm) -> uint32_t { return remap_in[nm]; };
  std::vector<uint8_t> emitted_group(ind_groups.size(), 0);
  size_t emitted_records = 0;

  for (size_t i = 0; i < decls.size(); i++) {
    if (!vis_decl[i]) continue;
    const DeclRec& d = decls[i];
    if (d.group_id != 0xFFFFFFFFu) {
      if (!emitted_group[d.group_id]) {
        emitted_group[d.group_id] = 1;
        std::string out_d = rewrite_decl_json(ind_groups[d.group_id].raw_line, map_final_cid, map_final_in, true);
        std::fwrite(out_d.data(), 1, out_d.size(), out_fp);
        emitted_records++;
      }
    } else {
      std::string out_d = rewrite_decl_json(d.raw_line, map_final_cid, map_final_in, true);
      std::fwrite(out_d.data(), 1, out_d.size(), out_fp);
      emitted_records++;
    }
  }

  std::fclose(out_fp);
  std::cerr << "Done! Emitted " << emitted_records << " fold records to " << out_path << "\n";
  return 0;
}
