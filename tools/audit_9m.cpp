#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct SMod {
  std::string name;
  int total_lines;
  int code_lines;
};

struct SDecl {
  uint32_t mod_idx;
  std::string kind;
  bool is_priv;
  std::string full_name;
  int start_line;
  int end_line;
};

static std::vector<std::string> split_char(const std::string& s, char delim) {
  std::vector<std::string> out;
  if (s.empty()) return out;
  size_t st = 0;
  while (st <= s.size()) {
    size_t p = s.find(delim, st);
    if (p == std::string::npos) { out.push_back(s.substr(st)); break; }
    out.push_back(s.substr(st, p - st));
    st = p + 1;
  }
  return out;
}

static std::string extract_private_mod(const std::string& kname, const std::unordered_set<std::string>& mod_set) {
  if (kname.compare(0, 9, "_private.") != 0) return "";
  size_t p1 = kname.find(".0.", 9);
  if (p1 == std::string::npos) return "";
  size_t mod_start = p1 + 3;
  size_t pos = mod_start;
  while (true) {
    size_t p2 = kname.find(".0.", pos);
    if (p2 == std::string::npos) break;
    std::string cand = kname.substr(mod_start, p2 - mod_start);
    if (mod_set.count(cand)) return cand;
    pos = p2 + 3;
  }
  return "";
}

static std::string short_name_of(const std::string& s) {
  size_t p = s.rfind('.');
  return (p == std::string::npos) ? s : s.substr(p + 1);
}

static bool has_clone_marker(const std::string& s) {
  // Check UTF-8 subscript 2/3 (\xe2\x82\x82, \xe2\x82\x83) or Copy/SideCopy/Alt/Shadow/Dup
  if (s.find("\xe2\x82\x82") != std::string::npos || s.find("\xe2\x82\x83") != std::string::npos) return true;
  const char* markers[] = {"Copy", "_copy", "SideCopy", "Alt", "_alt", "Shadow", "Clone", "Prime'", "₂", "2_"};
  for (const char* m : markers) {
    if (s.find(m) != std::string::npos) return true;
  }
  return false;
}

static bool has_bridge_marker(const std::string& s) {
  const char* markers[] = {
    "Bridge", "bridge", "Transfer", "transfer", "Transport", "transport",
    "Compat", "compat", "Equiv", "equiv", "Iso", "ToHost", "OfHost", "RawTo", "ToRaw"
  };
  for (const char* m : markers) {
    if (s.find(m) != std::string::npos) return true;
  }
  return false;
}

static uint64_t fnv1a_u32_vec(const std::vector<uint32_t>& v, uint64_t seed = 14695981039346656037ULL) {
  uint64_t h = seed;
  for (uint32_t x : v) {
    h ^= x;
    h *= 1099511628211ULL;
  }
  return h;
}

int main(int argc, char** argv) {
  if (argc < 7) {
    std::cerr << "Usage: audit_9m <lean.tar> <modules.tsv> <decls.tsv> <challenge_decls.tsv> <solution_decls.tsv> <solution_edges.bin>\n";
    return 1;
  }

  std::vector<SMod> smods;
  std::unordered_map<std::string, uint32_t> mod_to_idx;
  std::unordered_set<std::string> mod_set;
  {
    std::ifstream in(argv[2]);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      auto cols = split_char(line, '\t');
      if (cols.size() < 7) continue;
      uint32_t idx = (uint32_t)smods.size();
      smods.push_back({cols[0], std::stoi(cols[1]), std::stoi(cols[2])});
      mod_to_idx[cols[0]] = idx;
      mod_set.insert(cols[0]);
    }
  }

  std::vector<SDecl> sdecls;
  std::unordered_map<std::string, std::vector<uint32_t>> name_to_sdecls;
  std::vector<std::vector<uint32_t>> mod_sdecls(smods.size());
  {
    std::ifstream in(argv[3]);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      auto cols = split_char(line, '\t');
      if (cols.size() < 6) continue;
      auto mit = mod_to_idx.find(cols[0]);
      if (mit == mod_to_idx.end()) continue;
      uint32_t did = (uint32_t)sdecls.size();
      SDecl d{mit->second, cols[1], cols[2] == "1", cols[3], std::stoi(cols[4]), std::stoi(cols[5])};
      name_to_sdecls[d.full_name].push_back(did);
      mod_sdecls[mit->second].push_back(did);
      sdecls.push_back(std::move(d));
    }
  }

  std::unordered_set<std::string> challenge_names;
  {
    std::ifstream in(argv[4]);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      auto cols = split_char(line, '\t');
      if (cols.size() >= 10) challenge_names.insert(cols[9]);
    }
  }

  struct KRec {
    char kind;
    uint32_t type_ie, val_ie, own_nodes;
    std::string name;
  };
  std::vector<KRec> kdecls;
  std::unordered_map<std::string, uint32_t> kname_to_id;
  {
    std::ifstream in(argv[5]);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      auto cols = split_char(line, '\t');
      if (cols.size() < 10) continue;
      uint32_t id = (uint32_t)kdecls.size();
      kname_to_id[cols[9]] = id;
      kdecls.push_back({
        cols[1][0],
        (uint32_t)std::stoul(cols[5]),
        (uint32_t)std::stoul(cols[6]),
        (uint32_t)std::stoul(cols[7]),
        cols[9]
      });
    }
  }
  uint32_t nd = (uint32_t)kdecls.size();

  FILE* efp = std::fopen(argv[6], "rb");
  uint32_t nd_hdr = 0;
  std::fread(&nd_hdr, sizeof(uint32_t), 1, efp);
  std::vector<std::vector<uint32_t>> type_deps(nd), val_deps(nd);
  for (uint32_t i = 0; i < nd; i++) {
    uint32_t nt = 0, nv = 0;
    std::fread(&nt, sizeof(uint32_t), 1, efp);
    type_deps[i].resize(nt);
    if (nt) std::fread(type_deps[i].data(), sizeof(uint32_t), nt, efp);
    std::fread(&nv, sizeof(uint32_t), 1, efp);
    val_deps[i].resize(nv);
    if (nv) std::fread(val_deps[i].data(), sizeof(uint32_t), nv, efp);
  }
  std::fclose(efp);

  std::vector<int32_t> kdecl_to_sdecl(nd, -1), kdecl_to_smod(nd, -1);
  std::vector<uint8_t> is_challenge_kid(nd, 0);
  for (uint32_t i = 0; i < nd; i++) {
    const std::string& kn = kdecls[i].name;
    if (challenge_names.count(kn)) { is_challenge_kid[i] = 1; continue; }
    if (kn.compare(0, 9, "_private.") == 0) {
      std::string pm = extract_private_mod(kn, mod_set);
      if (!pm.empty()) {
        uint32_t mid = mod_to_idx[pm];
        kdecl_to_smod[i] = (int32_t)mid;
        std::string needle = ".0." + pm + ".0.";
        size_t p = kn.find(needle);
        if (p != std::string::npos) {
          std::string cur = kn.substr(p + needle.size());
          while (!cur.empty()) {
            auto it = name_to_sdecls.find(cur);
            if (it != name_to_sdecls.end()) {
              for (uint32_t sdid : it->second) if (sdecls[sdid].mod_idx == mid) { kdecl_to_sdecl[i] = (int32_t)sdid; break; }
              if (kdecl_to_sdecl[i] != -1) break;
            }
            size_t dot = cur.rfind('.');
            if (dot == std::string::npos) break;
            cur.resize(dot);
          }
        }
        continue;
      }
    }
    std::string cur = kn;
    while (!cur.empty()) {
      auto it = name_to_sdecls.find(cur);
      if (it != name_to_sdecls.end()) {
        kdecl_to_sdecl[i] = (int32_t)it->second[0];
        kdecl_to_smod[i] = (int32_t)sdecls[it->second[0]].mod_idx;
        break;
      }
      size_t dot = cur.rfind('.');
      if (dot == std::string::npos) break;
      cur.resize(dot);
    }
  }

  // Exact Def + Prop CSE reachability (matching compact_repo)
  std::unordered_map<uint64_t, uint32_t> first_def;
  std::unordered_map<uint32_t, uint32_t> first_thm;
  std::unordered_map<uint32_t, uint32_t> redirect;
  for (uint32_t i = 0; i < nd; i++) {
    if (kdecls[i].kind == 'd') {
      uint64_t key = ((uint64_t)kdecls[i].type_ie << 32) | kdecls[i].val_ie;
      auto [it, ins] = first_def.emplace(key, i);
      if (!ins) redirect[i] = it->second;
    } else if (kdecls[i].kind == 't') {
      auto [it, ins] = first_thm.emplace(kdecls[i].type_ie, i);
      if (!ins) redirect[i] = it->second;
    }
  }
  uint32_t root_kid = kname_to_id.at("riemannHypothesis");
  auto resolve = [&](uint32_t id) {
    if (id == root_kid) return id;
    auto it = redirect.find(id);
    while (it != redirect.end() && it->second != root_kid) {
      id = it->second;
      it = redirect.find(id);
    }
    return id;
  };

  std::vector<uint8_t> k_live(nd, 0);
  std::vector<uint8_t> sdecl_live(sdecls.size(), 0);
  std::vector<uint8_t> smod_live(smods.size(), 0);
  std::vector<uint32_t> k_in_deg(nd, 0);
  std::vector<uint32_t> k_cross_mod_callers(nd, 0);

  std::vector<uint32_t> q = {root_kid};
  k_live[root_kid] = 1;
  while (!q.empty()) {
    uint32_t u = q.back();
    q.pop_back();
    int32_t mu = kdecl_to_smod[u];
    std::unordered_set<uint32_t> seen_out;
    auto step = [&](uint32_t raw_v) {
      uint32_t v = resolve(raw_v);
      if (v != u && seen_out.insert(v).second) {
        k_in_deg[v]++;
        int32_t mv = kdecl_to_smod[v];
        if (mu >= 0 && mv >= 0 && mu != mv) k_cross_mod_callers[v]++;
      }
      if (!k_live[v]) { k_live[v] = 1; q.push_back(v); }
    };
    for (uint32_t rv : type_deps[u]) step(rv);
    for (uint32_t rv : val_deps[u]) step(rv);
  }

  // Map sdecl -> primary live kdecl and aggregate caller counts per sdecl
  std::vector<uint32_t> sdecl_callers(sdecls.size(), 0);
  std::vector<uint32_t> sdecl_cross_callers(sdecls.size(), 0);
  std::vector<int32_t> sdecl_rep_kid(sdecls.size(), -1);
  for (uint32_t i = 0; i < nd; i++) {
    if (!k_live[i]) continue;
    if (kdecl_to_smod[i] >= 0) smod_live[kdecl_to_smod[i]] = 1;
    if (kdecl_to_sdecl[i] >= 0) {
      int32_t primary = kdecl_to_sdecl[i];
      for (uint32_t sdid : name_to_sdecls[sdecls[primary].full_name]) {
        sdecl_live[sdid] = 1;
        smod_live[sdecls[sdid].mod_idx] = 1;
        sdecl_callers[sdid] += k_in_deg[i];
        sdecl_cross_callers[sdid] += k_cross_mod_callers[i];
        if (sdecl_rep_kid[sdid] == -1) sdecl_rep_kid[sdid] = (int32_t)i;
      }
    }
  }

  // Fuzzy / Shadow-Hierarchy CSE estimate on LIVE project kernel decls:
  // What if we signature each live project theorem/def by:
  //   (A) Exact sorted set of Mathlib/Core constants in `type_deps` + count of project constants in `type_deps` (with >= 2 Mathlib constants)
  //   (B) Same (A) PLUS identical short_name (e.g. two parallel namespaces proving `mem_nhds_zero` over clone project structs!)
  //   (C) Isomorphic project `structure`/`inductive` definitions (kind == 'i'): same sorted Mathlib `type_deps` + constructor count!
  std::unordered_map<uint64_t, uint32_t> skelA_first;
  std::unordered_map<uint64_t, uint32_t> skelB_first;
  std::unordered_map<uint64_t, uint32_t> ind_skel_first;
  std::vector<uint8_t> sdecl_shadow_strict(sdecls.size(), 0); // same short_name + same Mathlib type skeleton
  std::vector<uint8_t> sdecl_shadow_broad(sdecls.size(), 0);  // same Mathlib+arity type skeleton (>=3 mathlib deps)
  size_t dup_inductives = 0;

  // Count constructors per inductive
  std::unordered_map<std::string, uint32_t> ind_ctor_cnt;
  for (uint32_t i = 0; i < nd; i++) {
    if (kdecls[i].kind == 'c') {
      size_t dot = kdecls[i].name.rfind('.');
      if (dot != std::string::npos) ind_ctor_cnt[kdecls[i].name.substr(0, dot)]++;
    }
  }

  for (uint32_t i = 0; i < nd; i++) {
    if (!k_live[i] || is_challenge_kid[i] || kdecl_to_sdecl[i] < 0) continue;
    std::vector<uint32_t> mdeps;
    uint32_t pdeps = 0;
    for (uint32_t rv : type_deps[i]) {
      uint32_t v = resolve(rv);
      if (is_challenge_kid[v]) mdeps.push_back(v);
      else pdeps++;
    }
    std::sort(mdeps.begin(), mdeps.end());
    mdeps.erase(std::unique(mdeps.begin(), mdeps.end()), mdeps.end());

    if (kdecls[i].kind == 'i') {
      std::vector<uint32_t> sig = mdeps;
      sig.push_back(0xdeadbeefU);
      sig.push_back(ind_ctor_cnt[kdecls[i].name]);
      sig.push_back(pdeps);
      uint64_t h = fnv1a_u32_vec(sig);
      auto [it, ins] = ind_skel_first.emplace(h, i);
      if (!ins) dup_inductives++;
    }

    if (kdecls[i].kind == 't' || kdecls[i].kind == 'd') {
      std::vector<uint32_t> sig = mdeps;
      sig.push_back(0xabad1deaU);
      sig.push_back(pdeps);
      sig.push_back((uint32_t)kdecls[i].kind);
      uint64_t hA = fnv1a_u32_vec(sig);

      std::string sn = short_name_of(sdecls[kdecl_to_sdecl[i]].full_name);
      uint64_t hB = hA;
      for (unsigned char ch : sn) { hB ^= ch; hB *= 1099511628211ULL; }

      if (!mdeps.empty() || pdeps > 0) {
        auto [itB, insB] = skelB_first.emplace(hB, i);
        if (!insB && itB->second != i && kdecl_to_sdecl[itB->second] != kdecl_to_sdecl[i]) {
          sdecl_shadow_strict[kdecl_to_sdecl[i]] = 1;
        }
      }
      if (mdeps.size() >= 3) {
        auto [itA, insA] = skelA_first.emplace(hA, i);
        if (!insA && itA->second != i && kdecl_to_sdecl[itA->second] != kdecl_to_sdecl[i]) {
          sdecl_shadow_broad[kdecl_to_sdecl[i]] = 1;
        }
      }
    }
  }

  // Now scan lean.tar to measure exact cleaned source lines per live sdecl and inspect syntax inside live decls!
  std::vector<uint32_t> sdecl_clean_lines(sdecls.size(), 0);
  uint64_t total_clean_decl_lines = 0;
  uint64_t sig_lines = 0;           // header/type signature lines before `:= by` / `:=`
  uint64_t at_heavy_lines = 0;      // lines containing >= 3 `@` explicit applications
  uint64_t have_let_lines = 0;      // lines starting with `have `, `let `, `suffices `, `obtain `, `rcases `
  uint64_t calc_conv_lines = 0;     // `calc` / `conv` / `rw [` / `simp [` lines
  uint64_t have_count = 0;          // total `have` blocks inside live proofs!

  FILE* fp = std::fopen(argv[1], "rb");
  unsigned char hdr[512];
  std::vector<char> buf;
  std::string pending_longlink;

  while (std::fread(hdr, 1, 512, fp) == 512) {
    bool all_zero = true;
    for (int i = 0; i < 512; i++) if (hdr[i] != 0) { all_zero = false; break; }
    if (all_zero) continue;
    size_t sz = 0;
    for (int i = 124; i < 136 && hdr[i]; i++) if (hdr[i] >= '0' && hdr[i] <= '7') sz = (sz << 3) + (hdr[i] - '0');
    char typeflag = (char)hdr[156];
    std::string name;
    if (!pending_longlink.empty()) {
      name = pending_longlink;
      pending_longlink.clear();
    } else {
      std::string prefix((const char*)hdr + 345, strnlen((const char*)hdr + 345, 155));
      std::string base((const char*)hdr, strnlen((const char*)hdr, 100));
      name = prefix.empty() ? base : (prefix + "/" + base);
    }
    size_t padded = (sz + 511) & ~size_t(511);
    if (typeflag == 'L') {
      buf.resize(padded);
      if (padded > 0 && std::fread(buf.data(), 1, padded, fp) != padded) break;
      pending_longlink.assign(buf.data(), strnlen(buf.data(), sz));
      continue;
    }
    if (typeflag == 'x' || typeflag == 'g') {
      buf.resize(padded);
      if (padded > 0 && std::fread(buf.data(), 1, padded, fp) != padded) break;
      if (typeflag == 'x') {
        size_t pos = 0;
        while (pos < sz) {
          size_t sp = pos;
          while (sp < sz && buf[sp] >= '0' && buf[sp] <= '9') sp++;
          if (sp == pos || sp >= sz || buf[sp] != ' ') break;
          size_t rec_len = std::strtoul(std::string(buf.data() + pos, sp - pos).c_str(), nullptr, 10);
          if (rec_len == 0 || pos + rec_len > sz) break;
          std::string rec(buf.data() + sp + 1, pos + rec_len - (sp + 1) - 1);
          if (rec.compare(0, 5, "path=") == 0) pending_longlink = rec.substr(5);
          pos += rec_len;
        }
      }
      continue;
    }
    if (typeflag != '0' && typeflag != '\0') {
      if (padded > 0) std::fseek(fp, (long)padded, SEEK_CUR);
      continue;
    }
    const std::string pfx = "lean/src/";
    const std::string sfx = ".lean";
    if (name.size() <= pfx.size() + sfx.size() ||
        name.compare(0, pfx.size(), pfx) != 0 ||
        name.compare(name.size() - sfx.size(), sfx.size(), sfx) != 0) {
      if (padded > 0) std::fseek(fp, (long)padded, SEEK_CUR);
      continue;
    }
    std::string mod = name.substr(pfx.size(), name.size() - pfx.size() - sfx.size());
    for (char& ch : mod) if (ch == '/') ch = '.';
    auto mit = mod_to_idx.find(mod);
    if (mit == mod_to_idx.end() || !smod_live[mit->second]) {
      if (padded > 0) std::fseek(fp, (long)padded, SEEK_CUR);
      continue;
    }
    uint32_t mid = mit->second;
    buf.resize(padded);
    if (padded > 0 && std::fread(buf.data(), 1, padded, fp) != padded) break;

    std::vector<std::string_view> lines(1);
    size_t st = 0;
    for (size_t i = 0; i < sz; i++) {
      if (buf[i] == '\n') {
        lines.emplace_back(buf.data() + st, i - st);
        st = i + 1;
      }
    }
    if (st < sz) lines.emplace_back(buf.data() + st, sz - st);
    int nlines = (int)lines.size() - 1;

    std::vector<int32_t> line_owner(nlines + 1, -1);
    for (uint32_t sdid : mod_sdecls[mid]) {
      if (sdecl_live[sdid]) {
        for (int ln = sdecls[sdid].start_line; ln <= std::min(nlines, sdecls[sdid].end_line); ln++) {
          line_owner[ln] = (int32_t)sdid;
        }
      }
    }

    int block_comment_depth = 0;
    int32_t cur_decl = -1;
    bool in_proof_body = false;
    for (int ln = 1; ln <= nlines; ln++) {
      std::string_view sv = lines[ln];
      std::string cleaned;
      for (size_t i = 0; i < sv.size(); ) {
        if (block_comment_depth > 0) {
          if (i + 1 < sv.size() && sv[i] == '/' && sv[i + 1] == '-') { block_comment_depth++; i += 2; }
          else if (i + 1 < sv.size() && sv[i] == '-' && sv[i + 1] == '/') { block_comment_depth--; i += 2; }
          else i++;
          continue;
        }
        if (i + 1 < sv.size() && sv[i] == '/' && sv[i + 1] == '-') { block_comment_depth = 1; i += 2; continue; }
        if (i + 1 < sv.size() && sv[i] == '-' && sv[i + 1] == '-') break;
        if (sv[i] == '"') {
          cleaned.push_back(sv[i++]);
          while (i < sv.size() && sv[i] != '"') {
            if (sv[i] == '\\' && i + 1 < sv.size()) cleaned.push_back(sv[i++]);
            cleaned.push_back(sv[i++]);
          }
          if (i < sv.size()) cleaned.push_back(sv[i++]);
          continue;
        }
        cleaned.push_back(sv[i++]);
      }
      int32_t owner = line_owner[ln];
      if (owner < 0) continue;
      if (owner != cur_decl) {
        cur_decl = owner;
        in_proof_body = false;
      }
      size_t first_ns = cleaned.find_first_not_of(" \t\r");
      if (first_ns == std::string::npos) continue;
      std::string_view tr(cleaned.data() + first_ns, cleaned.size() - first_ns);

      sdecl_clean_lines[owner]++;
      total_clean_decl_lines++;

      int at_cnt = 0;
      for (char c : tr) if (c == '@') at_cnt++;
      if (at_cnt >= 3) at_heavy_lines++;

      if (!in_proof_body) {
        sig_lines++;
        if (tr.find(":= by") != std::string_view::npos || tr.find(":=") != std::string_view::npos || tr.substr(0, 6) == "where " || tr == "where") {
          in_proof_body = true;
        }
      } else {
        if (tr.substr(0, 5) == "have " || tr.substr(0, 5) == "have'") {
          have_let_lines++;
          have_count++;
        } else if (tr.substr(0, 4) == "let " || tr.substr(0, 9) == "suffices " ||
                   tr.substr(0, 7) == "obtain " || tr.substr(0, 7) == "rcases ") {
          have_let_lines++;
        } else if (tr.substr(0, 3) == "rw " || tr.substr(0, 4) == "rw[" ||
                   tr.substr(0, 5) == "simp " || tr.substr(0, 5) == "simp[" ||
                   tr.substr(0, 6) == "dsimp " || tr.substr(0, 5) == "erw [") {
          calc_conv_lines++;
        }
      }
    }
  }
  std::fclose(fp);

  // Aggregate declaration-level breakdowns!
  uint64_t live_sdecl_cnt = 0;
  uint64_t one_caller_cnt = 0, one_caller_lines = 0;
  uint64_t one_caller_same_mod_cnt = 0, one_caller_same_mod_lines = 0;
  uint64_t le2_caller_cnt = 0, le2_caller_lines = 0;
  uint64_t clone_name_cnt = 0, clone_name_lines = 0;
  uint64_t bridge_name_cnt = 0, bridge_name_lines = 0;
  uint64_t shadow_strict_cnt = 0, shadow_strict_lines = 0;
  uint64_t shadow_broad_cnt = 0, shadow_broad_lines = 0;
  uint64_t clone_or_bridge_or_shadow_lines = 0;

  // Short-name collision across different modules (same lemma name defined in 2+ live files!)
  std::unordered_map<std::string, std::vector<uint32_t>> short_name_groups;
  for (size_t d = 0; d < sdecls.size(); d++) {
    if (!sdecl_live[d]) continue;
    short_name_groups[short_name_of(sdecls[d].full_name)].push_back((uint32_t)d);
  }
  uint64_t dup_shortname_excess_decls = 0, dup_shortname_excess_lines = 0;
  for (auto& [sn, vec] : short_name_groups) {
    if (vec.size() >= 2) {
      // Sort descending so keep 1 canonical, count the excess copies
      uint64_t sum = 0, mx = 0;
      for (uint32_t d : vec) {
        sum += sdecl_clean_lines[d];
        mx = std::max<uint64_t>(mx, sdecl_clean_lines[d]);
      }
      dup_shortname_excess_decls += (vec.size() - 1);
      dup_shortname_excess_lines += (sum - mx);
    }
  }

  // Proof size buckets
  uint64_t lines_le_15 = 0, cnt_le_15 = 0;
  uint64_t lines_16_50 = 0, cnt_16_50 = 0;
  uint64_t lines_51_150 = 0, cnt_51_150 = 0;
  uint64_t lines_gt_150 = 0, cnt_gt_150 = 0;

  // Top-level directory breakdown of the 9.27M clean decl lines
  std::map<std::string, uint64_t> dir_lines;

  for (size_t d = 0; d < sdecls.size(); d++) {
    if (!sdecl_live[d]) continue;
    live_sdecl_cnt++;
    uint32_t L = sdecl_clean_lines[d];

    if (L <= 15) { cnt_le_15++; lines_le_15 += L; }
    else if (L <= 50) { cnt_16_50++; lines_16_50 += L; }
    else if (L <= 150) { cnt_51_150++; lines_51_150 += L; }
    else { cnt_gt_150++; lines_gt_150 += L; }

    const std::string& mname = smods[sdecls[d].mod_idx].name;
    auto parts = split_char(mname, '.');
    std::string bucket = parts[0];
    if (parts[0] == "Development" && parts.size() >= 2) bucket = "Development." + parts[1];
    dir_lines[bucket] += L;

    if (sdecl_callers[d] == 1) {
      one_caller_cnt++;
      one_caller_lines += L;
      if (sdecl_cross_callers[d] == 0) {
        one_caller_same_mod_cnt++;
        one_caller_same_mod_lines += L;
      }
    }
    if (sdecl_callers[d] >= 1 && sdecl_callers[d] <= 2) {
      le2_caller_cnt++;
      le2_caller_lines += L;
    }

    bool is_cl = has_clone_marker(sdecls[d].full_name) || has_clone_marker(mname);
    bool is_br = has_bridge_marker(sdecls[d].full_name) || has_bridge_marker(mname);
    bool is_ss = sdecl_shadow_strict[d] != 0;
    bool is_sb = sdecl_shadow_broad[d] != 0;

    if (is_cl) { clone_name_cnt++; clone_name_lines += L; }
    if (is_br) { bridge_name_cnt++; bridge_name_lines += L; }
    if (is_ss) { shadow_strict_cnt++; shadow_strict_lines += L; }
    if (is_sb) { shadow_broad_cnt++; shadow_broad_lines += L; }
    if (is_cl || is_br || is_sb) clone_or_bridge_or_shadow_lines += L;
  }

  auto pct = [&](uint64_t x) { return 100.0 * (double)x / (double)total_clean_decl_lines; };

  std::cout << std::fixed << std::setprecision(2);
  std::cout << "=== ANATOMY OF THE 9.28M SURVIVING CLEAN LINES ===\n";
  std::cout << "Total live source decls:       " << live_sdecl_cnt << "\n";
  std::cout << "Total clean decl code lines:   " << total_clean_decl_lines << "\n\n";

  std::cout << "--- 1. SINGLE-USE / STEPPING-STONE HELPER LEMMAS ---\n";
  std::cout << "  1-caller decls (used ONCE total):    " << one_caller_cnt << " decls | " << one_caller_lines << " lines (" << pct(one_caller_lines) << "%)\n";
  std::cout << "    of which private/same-file only:   " << one_caller_same_mod_cnt << " decls | " << one_caller_same_mod_lines << " lines (" << pct(one_caller_same_mod_lines) << "%)\n";
  std::cout << "  <=2-caller decls:                    " << le2_caller_cnt << " decls | " << le2_caller_lines << " lines (" << pct(le2_caller_lines) << "%)\n\n";

  std::cout << "--- 2. CLONE HIERARCHIES, SHADOW RE-PROOFS & TRANSPORT GLUE ---\n";
  std::cout << "  Isomorphic project struct/inductive: " << dup_inductives << " duplicate inductive/structure defs\n";
  std::cout << "  Explicit clone markers (*2/Copy/Alt):" << clone_name_cnt << " decls | " << clone_name_lines << " lines (" << pct(clone_name_lines) << "%)\n";
  std::cout << "  Bridge/Transfer/Compat/Equiv glue:   " << bridge_name_cnt << " decls | " << bridge_name_lines << " lines (" << pct(bridge_name_lines) << "%)\n";
  std::cout << "  Shadow strict (same shortname+skel): " << shadow_strict_cnt << " decls | " << shadow_strict_lines << " lines (" << pct(shadow_strict_lines) << "%)\n";
  std::cout << "  Shadow broad (same Mathlib+arity):   " << shadow_broad_cnt << " decls | " << shadow_broad_lines << " lines (" << pct(shadow_broad_lines) << "%)\n";
  std::cout << "  Same short-name excess across files: " << dup_shortname_excess_decls << " decls | " << dup_shortname_excess_lines << " lines (" << pct(dup_shortname_excess_lines) << "%)\n";
  std::cout << "  Union (clone | bridge | shadow):     " << clone_or_bridge_or_shadow_lines << " lines (" << pct(clone_or_bridge_or_shadow_lines) << "%)\n\n";

  std::cout << "--- 3. INSIDE-DECLARATION PROOF BLOAT (SYNTAX ANATOMY) ---\n";
  std::cout << "  Declaration headers / type sigs:     " << sig_lines << " lines (" << pct(sig_lines) << "%)\n";
  std::cout << "  Proof tactic / term bodies:          " << (total_clean_decl_lines - sig_lines) << " lines (" << pct(total_clean_decl_lines - sig_lines) << "%)\n";
  std::cout << "  Explicit `@`-storm lines (>=3 `@`s): " << at_heavy_lines << " lines (" << pct(at_heavy_lines) << "%)\n";
  std::cout << "  `have`/`let`/`obtain` opener lines:  " << have_let_lines << " lines (" << have_count << " `have` subgoals = " << ((double)have_count / live_sdecl_cnt) << " per decl!)\n";
  std::cout << "  `rw`/`simp`/`dsimp` rewrite lines:   " << calc_conv_lines << " lines (" << pct(calc_conv_lines) << "%)\n\n";

  std::cout << "--- 4. DECLARATION LENGTH DISTRIBUTION ---\n";
  std::cout << "  <= 15 lines:   " << cnt_le_15 << " decls | " << lines_le_15 << " lines (" << pct(lines_le_15) << "%)\n";
  std::cout << "  16..50 lines:  " << cnt_16_50 << " decls | " << lines_16_50 << " lines (" << pct(lines_16_50) << "%)\n";
  std::cout << "  51..150 lines: " << cnt_51_150 << " decls | " << lines_51_150 << " lines (" << pct(lines_51_150) << "%)\n";
  std::cout << "  > 150 lines:   " << cnt_gt_150 << " decls | " << lines_gt_150 << " lines (" << pct(lines_gt_150) << "%)\n\n";

  std::cout << "--- 5. TOP SUBSYSTEMS IN THE 9.27M CLEAN LINES ---\n";
  std::vector<std::pair<uint64_t, std::string>> sorted_dirs;
  for (auto& [k, v] : dir_lines) sorted_dirs.push_back({v, k});
  std::sort(sorted_dirs.rbegin(), sorted_dirs.rend());
  for (size_t i = 0; i < std::min<size_t>(18, sorted_dirs.size()); i++) {
    std::cout << "  " << std::setw(42) << std::left << sorted_dirs[i].second << " "
              << std::setw(10) << std::right << sorted_dirs[i].first << " (" << pct(sorted_dirs[i].first) << "%)\n";
  }
  return 0;
}
