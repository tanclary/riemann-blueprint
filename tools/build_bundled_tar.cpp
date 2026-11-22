#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

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

static void fill_ustar_header(unsigned char hdr[512], const std::string& name, const std::string& prefix,
                              size_t size, char typeflag) {
  std::memset(hdr, 0, 512);
  std::memcpy(hdr, name.data(), std::min<size_t>(100, name.size()));
  std::snprintf((char*)hdr + 100, 8, "%07o", 0644);
  std::snprintf((char*)hdr + 108, 8, "%07o", 0);
  std::snprintf((char*)hdr + 116, 8, "%07o", 0);
  std::snprintf((char*)hdr + 124, 12, "%011zo", size);
  std::snprintf((char*)hdr + 136, 12, "%011o", 017322000000);
  std::memset(hdr + 148, ' ', 8);
  hdr[156] = (unsigned char)typeflag;
  std::memcpy(hdr + 257, "ustar\0", 6);
  std::memcpy(hdr + 263, "00", 2);
  if (!prefix.empty()) {
    std::memcpy(hdr + 345, prefix.data(), std::min<size_t>(155, prefix.size()));
  }
  unsigned int sum = 0;
  for (int i = 0; i < 512; i++) sum += hdr[i];
  std::snprintf((char*)hdr + 148, 7, "%06o", sum);
  hdr[155] = ' ';
}

static void write_tar_file(FILE* out, const std::string& full_path, std::string_view content) {
  unsigned char hdr[512];
  static const unsigned char zeros[512] = {0};
  if (full_path.size() > 99) {
    std::string body = "path=" + full_path + "\n";
    size_t len = body.size() + 3;
    while (true) {
      std::string rec = std::to_string(len) + " " + body;
      if (rec.size() == len) {
        fill_ustar_header(hdr, "PaxHeader/entry", "", rec.size(), 'x');
        std::fwrite(hdr, 1, 512, out);
        std::fwrite(rec.data(), 1, rec.size(), out);
        size_t rem = (512 - (rec.size() & 511)) & 511;
        if (rem) std::fwrite(zeros, 1, rem, out);
        break;
      }
      len = rec.size();
    }
  }
  std::string prefix, base = full_path;
  if (full_path.size() > 100) {
    size_t slash = full_path.rfind('/');
    if (slash != std::string::npos && slash <= 155 && full_path.size() - slash - 1 <= 100) {
      prefix = full_path.substr(0, slash);
      base = full_path.substr(slash + 1);
    } else {
      base = full_path.substr(full_path.size() - 99);
    }
  }
  fill_ustar_header(hdr, base, prefix, content.size(), '0');
  std::fwrite(hdr, 1, 512, out);
  if (!content.empty()) {
    std::fwrite(content.data(), 1, content.size(), out);
    size_t rem = (512 - (content.size() & 511)) & 511;
    if (rem) std::fwrite(zeros, 1, rem, out);
  }
}

static std::string slurp_file(const std::string& p) {
  std::ifstream in(p, std::ios::binary);
  if (!in) return "";
  std::ostringstream ss;
  ss << in.rdbuf();
  return ss.str();
}

static std::string subsystem_prefix(const std::string& mod) {
  auto parts = split_char(mod, '.');
  if (parts.size() <= 1) return mod;
  if (parts.size() == 2) return parts[0];
  return parts[0] + "." + parts[1];
}

int main(int argc, char** argv) {
  if (argc < 9) {
    std::cerr << "Usage: build_bundled_tar <lean.tar> <modules.tsv> <decls.tsv> <challenge_decls.tsv> <solution_decls.tsv> <solution_edges.bin> <lean_root_dir> <out.tar.zst>\n";
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
  for (const char* rname : {"riemannHypothesis", "riemannZeta_eq_zero_re",
                            "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
                            "LFunction_eq_zero_re_of_isPrimitive"}) {
    challenge_names.erase(rname);
  }

  // Exact topological depth of every module from the acyclic source `import` graph!
  std::vector<int> mod_depth(smods.size(), -1);
  auto calc_src_depth = [&](uint32_t m, auto& self) -> int {
    if (mod_depth[m] >= 0) return mod_depth[m];
    mod_depth[m] = 0;
    int d = 0;
    for (const auto& imp : smods[m].imports) {
      auto it = mod_to_idx.find(imp);
      if (it != mod_to_idx.end()) d = std::max(d, 1 + self(it->second, self));
    }
    mod_depth[m] = d;
    return d;
  };
  for (size_t m = 0; m < smods.size(); m++) calc_src_depth((uint32_t)m, calc_src_depth);

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

  std::vector<uint32_t> q;
  for (const char* rname : {"riemannHypothesis", "riemannZeta_eq_zero_re",
                            "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
                            "LFunction_eq_zero_re_of_isPrimitive"}) {
    auto it = kname_to_id.find(rname);
    if (it != kname_to_id.end() && !k_live[it->second]) {
      k_live[it->second] = 1;
      q.push_back(it->second);
    }
  }
  while (!q.empty()) {
    uint32_t u = q.back();
    q.pop_back();
    int32_t mu = kdecl_to_smod[u];
    auto step = [&](uint32_t raw_v) {
      uint32_t v = resolve(raw_v);
      int32_t mv = kdecl_to_smod[v];
      // Preserve strict topological direction from `smods` DAG!
      if (mu >= 0 && mv >= 0 && mod_depth[mv] >= mod_depth[mu]) {
        v = raw_v;
        mv = kdecl_to_smod[raw_v];
      }
      if (mu >= 0 && mv >= 0 && mu != mv && mod_depth[mv] < mod_depth[mu]) {
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
  if (mod_to_idx.count("Main")) smod_live[mod_to_idx["Main"]] = 1;
  if (mod_to_idx.count("Statements")) smod_live[mod_to_idx["Statements"]] = 1;

  // Group live modules (except Main & Statements) into cycle-free DAG antichain bundles by (subsystem_prefix, depth)!
  // Because every module in `(subsys, depth)` has exact topological height `depth`, there are ZERO paths between any
  // two bundles at the same `depth` and every dependency strictly points to `dep_depth < depth` -> 100% cycle-free DAG!
  std::map<std::pair<std::string, int>, std::vector<uint32_t>> bundles;
  std::vector<std::string> mod_bundle_name(smods.size());

  for (size_t m = 0; m < smods.size(); m++) {
    if (!smod_live[m]) continue;
    if (smods[m].name == "Main" || smods[m].name == "Statements") {
      mod_bundle_name[m] = smods[m].name;
      continue;
    }
    bundles[{subsystem_prefix(smods[m].name), mod_depth[m]}].push_back((uint32_t)m);
  }

  struct BundleInfo {
    std::string bname;
    std::string path;
    int depth;
    std::vector<uint32_t> members;
  };
  std::vector<BundleInfo> all_bundles;
  std::unordered_map<std::string, uint32_t> bname_to_idx;

  // Split huge antichains (> 4000 lines or > 80 modules) into ~3000-line shards `Layer003_A.lean`, `Layer003_B.lean`!
  for (auto& [key, mems] : bundles) {
    std::sort(mems.begin(), mems.end(), [&](uint32_t a, uint32_t b) { return smods[a].name < smods[b].name; });
    const std::string& sub = key.first;
    int d = key.second;
    std::vector<std::vector<uint32_t>> shards;
    int cur_lines = 0;
    for (uint32_t m : mems) {
      if (shards.empty() || cur_lines + smods[m].code_lines > 3500 || shards.back().size() >= 80) {
        shards.emplace_back();
        cur_lines = 0;
      }
      shards.back().push_back(m);
      cur_lines += smods[m].code_lines;
    }
    for (size_t s = 0; s < shards.size(); s++) {
      char lbuf[64];
      if (shards.size() == 1) std::snprintf(lbuf, sizeof(lbuf), "Layer%03d", d);
      else std::snprintf(lbuf, sizeof(lbuf), "Layer%03d_%02zu", d, s + 1);
      std::string bname = sub + "." + lbuf;
      std::string bpath = "lean/src/" + bname;
      for (size_t k = 9; k < bpath.size(); k++) if (bpath[k] == '.') bpath[k] = '/';
      bpath += ".lean";
      uint32_t bidx = (uint32_t)all_bundles.size();
      bname_to_idx[bname] = bidx;
      for (uint32_t m : shards[s]) mod_bundle_name[m] = bname;
      all_bundles.push_back({bname, bpath, d, std::move(shards[s])});
    }
  }

  // Read cleaned body of each live module from `lean.tar`
  std::vector<std::string> mod_body(smods.size());
  std::string raw_main, raw_statements;

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

    if (mod == "Main") { raw_main.assign(buf.data(), sz); continue; }
    if (mod == "Statements") { raw_statements.assign(buf.data(), sz); continue; }

    std::vector<std::string_view> lines(1);
    size_t st = 0;
    for (size_t i = 0; i < sz; i++) {
      if (buf[i] == '\n') { lines.emplace_back(buf.data() + st, i - st); st = i + 1; }
    }
    if (st < sz) lines.emplace_back(buf.data() + st, sz - st);
    int nlines = (int)lines.size() - 1;

    std::vector<uint8_t> dead_line(nlines + 1, 0), in_live_decl(nlines + 1, 0);
    for (uint32_t sdid : mod_sdecls[mid]) {
      if (!sdecl_live[sdid]) {
        for (int ln = sdecls[sdid].start_line; ln <= std::min(nlines, sdecls[sdid].end_line); ln++) dead_line[ln] = 1;
      } else {
        for (int ln = sdecls[sdid].start_line; ln <= std::min(nlines, sdecls[sdid].end_line); ln++) in_live_decl[ln] = 1;
      }
    }

    std::string body;
    std::vector<std::string> open_scopes;
    int block_comment_depth = 0;
    for (int ln = 1; ln <= nlines; ln++) {
      if (dead_line[ln] && !in_live_decl[ln]) continue;
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
      while (!cleaned.empty() && (cleaned.back() == ' ' || cleaned.back() == '\t' || cleaned.back() == '\r')) cleaned.pop_back();
      size_t first_ns = cleaned.find_first_not_of(" \t");
      if (first_ns == std::string::npos) continue;
      std::string_view trimmed(cleaned.data() + first_ns, cleaned.size() - first_ns);
      if (trimmed.substr(0, 7) == "import ") continue;
      // Track top-level namespace / section blocks so EOF-implicitly-closed scopes are closed before next bundle member!
      if (first_ns == 0) {
        if (trimmed.substr(0, 10) == "namespace ") {
          open_scopes.emplace_back(trimmed.substr(10));
        } else if (trimmed == "section" || trimmed == "noncomputable section") {
          open_scopes.emplace_back("");
        } else if (trimmed.substr(0, 8) == "section ") {
          open_scopes.emplace_back(trimmed.substr(8));
        } else if (trimmed.substr(0, 22) == "noncomputable section ") {
          open_scopes.emplace_back(trimmed.substr(22));
        } else if (trimmed == "end") {
          if (!open_scopes.empty()) open_scopes.pop_back();
        } else if (trimmed.substr(0, 4) == "end ") {
          std::string target(trimmed.substr(4));
          while (!open_scopes.empty()) {
            std::string top = std::move(open_scopes.back());
            open_scopes.pop_back();
            if (top == target) break;
          }
        }
      }
      body += cleaned + "\n";
    }
    while (!open_scopes.empty()) {
      std::string top = std::move(open_scopes.back());
      open_scopes.pop_back();
      if (top.empty()) body += "end\n";
      else body += "end " + top + "\n";
    }
    mod_body[mid] = std::move(body);
  }
  std::fclose(fp);

  // Build bundle-level DAG and transitively reduce bundle imports!
  size_t nb = all_bundles.size();
  std::vector<std::unordered_set<uint32_t>> b_deps(nb);
  for (size_t b = 0; b < nb; b++) {
    for (uint32_t m : all_bundles[b].members) {
      for (uint32_t dep_m : req_mod_imports[m]) {
        const std::string& dbn = mod_bundle_name[dep_m];
        auto bit = bname_to_idx.find(dbn);
        if (bit != bname_to_idx.end() && bit->second != b) b_deps[b].insert(bit->second);
      }
    }
  }

  // Topological order on bundles (already sorted by depth!) for exact transitive reduction
  std::vector<uint32_t> order(nb);
  for (size_t i = 0; i < nb; i++) order[i] = (uint32_t)i;
  std::sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) { return all_bundles[a].depth < all_bundles[b].depth; });

  std::vector<std::vector<uint32_t>> b_min_deps(nb);
  std::vector<uint32_t> stamp(nb, 0);
  uint32_t cur_tag = 0;
  uint64_t total_bundle_imports = 0;
  for (uint32_t b : order) {
    cur_tag++;
    std::vector<uint32_t> qbfs;
    for (uint32_t d1 : b_deps[b]) {
      for (uint32_t d2 : b_deps[d1]) {
        if (stamp[d2] != cur_tag) { stamp[d2] = cur_tag; qbfs.push_back(d2); }
      }
    }
    for (size_t qi = 0; qi < qbfs.size(); qi++) {
      for (uint32_t d3 : b_deps[qbfs[qi]]) {
        if (stamp[d3] != cur_tag) { stamp[d3] = cur_tag; qbfs.push_back(d3); }
      }
    }
    for (uint32_t d1 : b_deps[b]) {
      if (stamp[d1] != cur_tag) b_min_deps[b].push_back(d1);
    }
    std::sort(b_min_deps[b].begin(), b_min_deps[b].end(), [&](uint32_t a, uint32_t c) {
      return all_bundles[a].bname < all_bundles[c].bname;
    });
    total_bundle_imports += b_min_deps[b].size();
  }

  std::string lean_root = argv[7];
  std::string out_zst = argv[8];
  FILE* zout = popen(("zstd -15 -T0 -f -o \"" + out_zst + "\"").c_str(), "w");
  if (!zout) { std::perror("popen zstd"); return 1; }

  for (const char* cfg : {"lakefile.toml", "lake-manifest.json", "lean-toolchain", "src/Blueprint.lean"}) {
    std::string content = slurp_file(lean_root + "/" + cfg);
    if (!content.empty()) write_tar_file(zout, std::string("lean/") + cfg, content);
  }

  uint64_t total_lines = 0, total_files = 0;
  for (size_t b = 0; b < nb; b++) {
    std::string txt;
    if (b_min_deps[b].empty()) {
      txt += "import Mathlib\n";
    } else {
      for (uint32_t dep_b : b_min_deps[b]) {
        txt += "import " + all_bundles[dep_b].bname + "\n";
      }
    }
    std::unordered_set<std::string> ext_imps;
    for (uint32_t m : all_bundles[b].members) {
      for (const auto& ri : smods[m].imports) {
        if (!mod_set.count(ri) && ri != "Mathlib") ext_imps.insert(ri);
      }
    }
    for (const auto& ei : ext_imps) txt += "import " + ei + "\n";

    for (uint32_t m : all_bundles[b].members) {
      if (all_bundles[b].members.size() > 1) {
        txt += "section\n";
        txt += mod_body[m];
        txt += "end\n";
      } else {
        txt += mod_body[m];
      }
    }
    for (char c : txt) if (c == '\n') total_lines++;
    write_tar_file(zout, all_bundles[b].path, txt);
    total_files++;
  }

  // Rewrite imports in Main.lean to bundle names!
  if (!raw_statements.empty()) {
    write_tar_file(zout, "lean/src/Statements.lean", raw_statements);
    for (char c : raw_statements) if (c == '\n') total_lines++;
    total_files++;
  }
  if (mod_to_idx.count("Main")) {
    uint32_t main_id = mod_to_idx["Main"];
    std::unordered_set<std::string> main_bdeps;
    std::string main_txt = "import Statements\n";
    for (uint32_t dep_m : req_mod_imports[main_id]) {
      if (!mod_bundle_name[dep_m].empty() && mod_bundle_name[dep_m] != "Statements") {
        main_bdeps.insert(mod_bundle_name[dep_m]);
      }
    }
    for (const auto& mb : main_bdeps) main_txt += "import " + mb + "\n";
    std::istringstream iss(raw_main);
    std::string ln;
    while (std::getline(iss, ln)) {
      if (ln.compare(0, 7, "import ") == 0) continue;
      main_txt += ln + "\n";
    }
    write_tar_file(zout, "lean/src/Main.lean", main_txt);
    for (char c : main_txt) if (c == '\n') total_lines++;
    total_files++;
  }

  unsigned char eof_zeros[1024] = {0};
  std::fwrite(eof_zeros, 1, 1024, zout);
  pclose(zout);

  std::cout << "=== BUNDLED SKINNY REPOSITORY SUMMARY ===\n"
            << "  Coalesced .lean files: " << total_files << " (down from 175,187 = -"
            << (100.0 * (175187.0 - total_files) / 175187.0) << "%!)\n"
            << "  Project import edges:  " << total_bundle_imports << " (down from 719,897 = -"
            << (100.0 * (719897.0 - total_bundle_imports) / 719897.0) << "%!)\n"
            << "  Total lines (all-in):  " << total_lines << " (down from 17,374,215 = -"
            << (100.0 * (17374215.0 - total_lines) / 17374215.0) << "%!)\n";
  return 0;
}
