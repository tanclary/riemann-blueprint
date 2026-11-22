#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace fs = std::filesystem;

struct SMod {
  std::string name;
  int total_lines;
  int code_lines;
  bool has_syntax_or_attr;
  std::vector<std::string> imports;
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

int main(int argc, char** argv) {
  if (argc < 7) {
    std::cerr << "Usage: compact_repo <lean.tar> <modules.tsv> <decls.tsv> <challenge_decls.tsv> <solution_decls.tsv> <solution_edges.bin> [out_tar_path]\n";
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
      smods.push_back({cols[0], std::stoi(cols[1]), std::stoi(cols[2]), cols[5] == "1", split_char(cols[6], ',')});
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
    uint32_t type_ie, val_ie;
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
      kdecls.push_back({cols[1][0], (uint32_t)std::stoul(cols[5]), (uint32_t)std::stoul(cols[6]), cols[9]});
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

  // Map kdecl -> sdecl / smod
  std::vector<int32_t> kdecl_to_sdecl(nd, -1), kdecl_to_smod(nd, -1);
  for (uint32_t i = 0; i < nd; i++) {
    const std::string& kn = kdecls[i].name;
    if (challenge_names.count(kn)) continue;
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

  // Def + Prop CSE reachability from riemannHypothesis
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
  std::vector<std::unordered_set<uint32_t>> req_mod_imports(smods.size());

  std::vector<uint32_t> q = {root_kid};
  k_live[root_kid] = 1;
  while (!q.empty()) {
    uint32_t u = q.back();
    q.pop_back();
    int32_t mu = kdecl_to_smod[u];
    auto step = [&](uint32_t raw_v) {
      uint32_t v = resolve(raw_v);
      int32_t mv = kdecl_to_smod[v];
      if (mu >= 0 && mv >= 0 && mu != mv) {
        req_mod_imports[mu].insert((uint32_t)mv);
      }
      if (!k_live[v]) { k_live[v] = 1; q.push_back(v); }
    };
    for (uint32_t rv : type_deps[u]) step(rv);
    for (uint32_t rv : val_deps[u]) step(rv);
  }

  for (uint32_t i = 0; i < nd; i++) {
    if (!k_live[i]) continue;
    if (kdecl_to_smod[i] >= 0) smod_live[kdecl_to_smod[i]] = 1;
    if (kdecl_to_sdecl[i] >= 0) {
      for (uint32_t sdid : name_to_sdecls[sdecls[kdecl_to_sdecl[i]].full_name]) {
        sdecl_live[sdid] = 1;
        smod_live[sdecls[sdid].mod_idx] = 1;
      }
    }
  }
  // Always keep Main and Statements
  if (mod_to_idx.count("Main")) smod_live[mod_to_idx["Main"]] = 1;
  if (mod_to_idx.count("Statements")) smod_live[mod_to_idx["Statements"]] = 1;

  // Transitive reduction on req_mod_imports[m]: if A needs B and C, and B already transitively imports C, drop C!
  // Compute topological order of req_mod_imports (since kernel deps are acyclic!)
  // Wait: let's just check direct 2-hop / 3-hop redundancy on req_mod_imports (fast & exact enough, or bitset on SCC-free DAG):
  size_t raw_live_imp_edges = 0, tr_live_imp_edges = 0;
  std::vector<std::vector<uint32_t>> min_imports(smods.size());
  {
    std::vector<uint32_t> imp_stamp(smods.size(), 0);
    uint32_t cur_imp_tag = 0;
    std::vector<uint32_t> bfs;
    for (size_t m = 0; m < smods.size(); m++) {
      if (!smod_live[m]) continue;
      raw_live_imp_edges += req_mod_imports[m].size();
      cur_imp_tag++;
      bfs.clear();
      for (uint32_t nb : req_mod_imports[m]) {
        for (uint32_t nb2 : req_mod_imports[nb]) {
          if (imp_stamp[nb2] != cur_imp_tag) {
            imp_stamp[nb2] = cur_imp_tag;
            bfs.push_back(nb2);
          }
        }
      }
      for (size_t bi = 0; bi < bfs.size() && bi < 2048; bi++) {
        for (uint32_t nb3 : req_mod_imports[bfs[bi]]) {
          if (imp_stamp[nb3] != cur_imp_tag) {
            imp_stamp[nb3] = cur_imp_tag;
            bfs.push_back(nb3);
          }
        }
      }
      for (uint32_t nb : req_mod_imports[m]) {
        if (imp_stamp[nb] != cur_imp_tag) min_imports[m].push_back(nb);
      }
      std::sort(min_imports[m].begin(), min_imports[m].end());
      tr_live_imp_edges += min_imports[m].size();
    }
  }

  // ALSO measure "The Annals Paper Core": what if classical Published Literature theorems
  // (UpperTheory.LiteratureTheorems.*_of_literature, *_of_open, GlobalTheory.Published.*, PublishedTheorems.*)
  // are treated as cited literature axioms (keeping their type_deps + all definitions, cutting only their proof val_deps)?
  {
    auto is_lit_citation = [&](uint32_t kid) -> bool {
      if (kdecls[kid].kind != 't') return false;
      const std::string& n = kdecls[kid].name;
      if (n.find("every_character") != std::string::npos || n.find("everyCharacter") != std::string::npos) return false;
      if (n.compare(0, 31, "UpperTheory.LiteratureTheorems.") == 0) return true;
      int32_t mid = kdecl_to_smod[kid];
      if (mid >= 0) {
        const std::string& mn = smods[mid].name;
        if (mn.find(".PublishedTheorems.") != std::string::npos) return true;
        if (mn.compare(0, 35, "Development.ResolutionOfSingularities") == 0) return true;
      }
      return false;
    };

    std::vector<uint8_t> k_new(nd, 0);
    std::vector<uint8_t> sdecl_new(sdecls.size(), 0);
    std::vector<uint8_t> smod_new(smods.size(), 0);
    std::vector<uint32_t> q2 = {root_kid};
    k_new[root_kid] = 1;
    size_t lit_axioms_hit = 0;
    while (!q2.empty()) {
      uint32_t u = q2.back();
      q2.pop_back();
      for (uint32_t rv : type_deps[u]) {
        uint32_t v = resolve(rv);
        if (!k_new[v]) { k_new[v] = 1; q2.push_back(v); }
      }
      if (is_lit_citation(u)) {
        lit_axioms_hit++;
        continue;  // cite classical theorem without stepping into its proof!
      }
      for (uint32_t rv : val_deps[u]) {
        uint32_t v = resolve(rv);
        if (!k_new[v]) { k_new[v] = 1; q2.push_back(v); }
      }
    }
    for (uint32_t i = 0; i < nd; i++) {
      if (!k_new[i]) continue;
      if (kdecl_to_smod[i] >= 0) smod_new[kdecl_to_smod[i]] = 1;
      if (kdecl_to_sdecl[i] >= 0) {
        for (uint32_t sdid : name_to_sdecls[sdecls[kdecl_to_sdecl[i]].full_name]) {
          sdecl_new[sdid] = 1;
          smod_new[sdecls[sdid].mod_idx] = 1;
        }
      }
    }
    size_t nmc = 0, ndc = 0;
    uint64_t ndl = 0;
    for (size_t m = 0; m < smods.size(); m++) if (smod_new[m]) nmc++;
    for (size_t d = 0; d < sdecls.size(); d++) if (sdecl_new[d]) { ndc++; ndl += std::max(1, sdecls[d].end_line - sdecls[d].start_line + 1); }
    std::cout << "=== LITERATURE CITATION SPLIT ('THE ANNALS PAPER CORE') ===\n";
    std::cout << "  Cited classical literature theorems hit: " << lit_axioms_hit << "\n";
    std::cout << "  New-RH-only modules:      " << nmc << " / " << smods.size() << "\n";
    std::cout << "  New-RH-only declarations: " << ndc << " / " << sdecls.size() << "\n";
    std::cout << "  New-RH-only decl lines:   " << ndl << " (meaning ~" << (9958417ULL - ndl)
              << " live lines are purely re-proving classical 20th/21st-century literature!)\n\n";
  }

  // Scan lean.tar and physically compact every live module!
  FILE* fp = std::fopen(argv[1], "rb");
  unsigned char hdr[512];
  std::vector<char> buf;
  std::string pending_longlink;

  uint64_t kept_files = 0;
  uint64_t out_lines_total = 0;
  uint64_t out_import_lines = 0;
  uint64_t out_header_lines = 0;
  uint64_t out_decl_code_lines = 0;
  uint64_t out_bytes_total = 0;

  std::string out_dir = (argc >= 8) ? argv[7] : "";
  if (!out_dir.empty()) fs::create_directories(out_dir);

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

    // Split file into 1-indexed lines
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

    // Mark dead declaration line spans!
    // Note: keep non-declaration lines (open, variable, namespace, end, attribute, set_option, notation, macro)!
    std::vector<uint8_t> dead_line(nlines + 1, 0);
    for (uint32_t sdid : mod_sdecls[mid]) {
      if (!sdecl_live[sdid]) {
        for (int ln = sdecls[sdid].start_line; ln <= std::min(nlines, sdecls[sdid].end_line); ln++) {
          dead_line[ln] = 1;
        }
      }
    }
    std::vector<uint8_t> in_live_decl(nlines + 1, 0);
    for (uint32_t sdid : mod_sdecls[mid]) {
      if (sdecl_live[sdid]) {
        for (int ln = sdecls[sdid].start_line; ln <= std::min(nlines, sdecls[sdid].end_line); ln++) {
          in_live_decl[ln] = 1;
        }
      }
    }

    // Build compacted file text:
    // 1. Minimal transitive-reduced imports (+ Mathlib if no project imports, plus any non-project imports like Lean.*)
    std::string out_txt;
    if (min_imports[mid].empty()) {
      out_txt += "import Mathlib\n";
      out_import_lines++;
      out_lines_total++;
    } else {
      for (uint32_t imp_mid : min_imports[mid]) {
        out_txt += "import " + smods[imp_mid].name + "\n";
        out_import_lines++;
        out_lines_total++;
      }
    }
    for (const auto& raw_imp : smods[mid].imports) {
      if (!mod_set.count(raw_imp) && raw_imp != "Mathlib") {
        out_txt += "import " + raw_imp + "\n";
        out_import_lines++;
        out_lines_total++;
      }
    }

    // 2. Emit non-import, non-comment, non-blank, non-dead_line lines!
    int block_comment_depth = 0;
    for (int ln = 1; ln <= nlines; ln++) {
      if (dead_line[ln] && !in_live_decl[ln]) continue;
      std::string_view sv = lines[ln];
      // Strip comments on this line while respecting nested /- ... -/ and strings
      std::string cleaned;
      for (size_t i = 0; i < sv.size(); ) {
        if (block_comment_depth > 0) {
          if (i + 1 < sv.size() && sv[i] == '/' && sv[i + 1] == '-') { block_comment_depth++; i += 2; }
          else if (i + 1 < sv.size() && sv[i] == '-' && sv[i + 1] == '/') { block_comment_depth--; i += 2; }
          else i++;
          continue;
        }
        if (i + 1 < sv.size() && sv[i] == '/' && sv[i + 1] == '-') { block_comment_depth = 1; i += 2; continue; }
        if (i + 1 < sv.size() && sv[i] == '-' && sv[i + 1] == '-') break;  // line comment
        if (sv[i] == '"') {
          cleaned.push_back(sv[i++]);
          while (i < sv.size() && sv[i] != '"') {
            if (sv[i] == '\\' && i + 1 < sv.size()) { cleaned.push_back(sv[i++]); }
            cleaned.push_back(sv[i++]);
          }
          if (i < sv.size()) cleaned.push_back(sv[i++]);
          continue;
        }
        cleaned.push_back(sv[i++]);
      }
      // Trim trailing whitespace
      while (!cleaned.empty() && (cleaned.back() == ' ' || cleaned.back() == '\t' || cleaned.back() == '\r')) cleaned.pop_back();
      size_t first_ns = cleaned.find_first_not_of(" \t");
      if (first_ns == std::string::npos) continue;  // blank line
      std::string_view trimmed(cleaned.data() + first_ns, cleaned.size() - first_ns);
      if (trimmed.substr(0, 7) == "import ") continue;  // replaced by minimal imports!

      out_txt += cleaned + "\n";
      out_lines_total++;
      if (in_live_decl[ln]) out_decl_code_lines++;
      else out_header_lines++;
    }

    kept_files++;
    out_bytes_total += out_txt.size();
  }
  std::fclose(fp);

  std::cout << "=== COMPACTED SOURCE REPOSITORY METRICS ===\n";
  std::cout << "  Kept .lean files:            " << kept_files << " / " << smods.size()
            << " (-" << (100.0 * (smods.size() - kept_files) / smods.size()) << "%)\n";
  std::cout << "  Project import edges (raw->TR): " << raw_live_imp_edges << " -> " << tr_live_imp_edges
            << " (vs 719,897 original = -" << (100.0 * (719897.0 - tr_live_imp_edges) / 719897.0) << "%!)\n";
  std::cout << "  Compacted total lines:       " << out_lines_total << " / 17,374,215"
            << " (-" << (100.0 * (17374215.0 - out_lines_total) / 17374215.0) << "%!)\n";
  std::cout << "    - Minimal import lines:    " << out_import_lines << "\n";
  std::cout << "    - Scope/open/option lines: " << out_header_lines << "\n";
  std::cout << "    - Live decl code lines:    " << out_decl_code_lines << "\n";
  std::cout << "  Compacted source bytes:      " << (out_bytes_total / (1024.0 * 1024.0)) << " MiB\n";
  std::cout << "  If coalesced into single-namespace packages (eliminating per-file import+open+ns boilerplate):\n";
  std::cout << "    - Coalesced LOC:           ~" << (out_decl_code_lines + 15000) << " lines (-"
            << (100.0 * (17374215.0 - (out_decl_code_lines + 15000)) / 17374215.0) << "%!)\n";
  return 0;
}
