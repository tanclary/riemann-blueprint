#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <functional>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct KDecl {
  uint32_t id;
  char kind;
  bool in_all5;
  bool in_rh;
  bool in_rh_stmt;
  uint32_t type_ie;
  uint32_t val_ie;
  uint32_t own_nodes;
  std::string type_hash;
  std::string name;
};

struct SMod {
  std::string name;
  int total_lines;
  int code_lines;
  int num_imports;
  int num_decls;
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
  int code_lines_est() const { return std::max(1, end_line - start_line + 1); }
};

static std::vector<std::string> split_char(const std::string& s, char delim) {
  std::vector<std::string> out;
  if (s.empty()) return out;
  size_t st = 0;
  while (st <= s.size()) {
    size_t p = s.find(delim, st);
    if (p == std::string::npos) {
      out.push_back(s.substr(st));
      break;
    }
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

// Lengauer-Tarjan Dominator Tree on directed graph adj[0..N-1] rooted at root_idx = 0
struct DominatorTree {
  int n;
  std::vector<int> dfn, rev_dfn, parent, sdom, idom, dsu_fa, dsu_best;
  std::vector<std::vector<int>> r_adj, bucket;
  int timer = 0;

  DominatorTree(int n_)
      : n(n_),
        dfn(n_, -1),
        rev_dfn(n_, -1),
        parent(n_, -1),
        sdom(n_, 0),
        idom(n_, -1),
        dsu_fa(n_, 0),
        dsu_best(n_, 0),
        r_adj(n_),
        bucket(n_) {}

  int find(int x) {
    if (dsu_fa[x] == x) return x;
    int r = find(dsu_fa[x]);
    if (dfn[sdom[dsu_best[dsu_fa[x]]]] < dfn[sdom[dsu_best[x]]]) {
      dsu_best[x] = dsu_best[dsu_fa[x]];
    }
    return dsu_fa[x] = r;
  }

  void build(int root, const std::vector<std::vector<int>>& adj) {
    // Iterative DFS to avoid stack overflow on deep proof chains!
    struct Frame { int u; size_t idx; };
    std::vector<Frame> st;
    dfn[root] = timer;
    rev_dfn[timer] = root;
    timer++;
    st.push_back({root, 0});
    while (!st.empty()) {
      Frame& fr = st.back();
      int u = fr.u;
      if (fr.idx < adj[u].size()) {
        int v = adj[u][fr.idx++];
        if (dfn[v] == -1) {
          parent[v] = u;
          dfn[v] = timer;
          rev_dfn[timer] = v;
          timer++;
          st.push_back({v, 0});
        }
      } else {
        st.pop_back();
      }
    }

    for (int u = 0; u < n; u++) {
      if (dfn[u] == -1) continue;
      sdom[u] = dsu_fa[u] = dsu_best[u] = u;
      for (int v : adj[u]) {
        if (dfn[v] != -1) r_adj[v].push_back(u);
      }
    }

    for (int i = timer - 1; i >= 1; i--) {
      int u = rev_dfn[i];
      for (int v : r_adj[u]) {
        if (dfn[v] < dfn[u]) {
          if (dfn[v] < dfn[sdom[u]]) sdom[u] = v;
        } else {
          find(v);
          int cand = sdom[dsu_best[v]];
          if (dfn[cand] < dfn[sdom[u]]) sdom[u] = cand;
        }
      }
      bucket[sdom[u]].push_back(u);
      dsu_fa[u] = parent[u];
      int p = parent[u];
      for (int w : bucket[p]) {
        find(w);
        int y = dsu_best[w];
        if (sdom[y] == sdom[w]) idom[w] = p;
        else idom[w] = y;  // deferred
      }
      bucket[p].clear();
    }

    for (int i = 1; i < timer; i++) {
      int u = rev_dfn[i];
      if (idom[u] != sdom[u]) idom[u] = idom[idom[u]];
    }
    idom[root] = root;
  }
};

int main(int argc, char** argv) {
  if (argc < 7) {
    std::cerr << "Usage: dominators <modules.tsv> <decls.tsv> <challenge_decls.tsv> <solution_decls.tsv> <solution_edges.bin> <out_dom.tsv>\n";
    return 1;
  }

  // Load modules
  std::vector<SMod> smods;
  std::unordered_map<std::string, uint32_t> mod_to_idx;
  std::unordered_set<std::string> mod_set;
  {
    std::ifstream in(argv[1]);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      auto cols = split_char(line, '\t');
      if (cols.size() < 7) continue;
      uint32_t idx = (uint32_t)smods.size();
      SMod m{cols[0], std::stoi(cols[1]), std::stoi(cols[2]), std::stoi(cols[3]),
             std::stoi(cols[4]), cols[5] == "1", split_char(cols[6], ',')};
      mod_to_idx[m.name] = idx;
      mod_set.insert(m.name);
      smods.push_back(std::move(m));
    }
  }

  // Load source decls
  std::vector<SDecl> sdecls;
  std::unordered_map<std::string, std::vector<uint32_t>> name_to_sdecls;
  {
    std::ifstream in(argv[2]);
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
      sdecls.push_back(std::move(d));
    }
  }

  // Challenge names
  std::unordered_set<std::string> challenge_names;
  {
    std::ifstream in(argv[3]);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      auto cols = split_char(line, '\t');
      if (cols.size() >= 10) challenge_names.insert(cols[9]);
    }
  }

  // Solution kdecls
  std::vector<KDecl> kdecls;
  std::unordered_map<std::string, uint32_t> kname_to_id;
  {
    std::ifstream in(argv[4]);
    std::string line;
    std::getline(in, line);
    while (std::getline(in, line)) {
      auto cols = split_char(line, '\t');
      if (cols.size() < 10) continue;
      KDecl d{(uint32_t)std::stoul(cols[0]), cols[1][0], cols[2] == "1", cols[3] == "1",
              cols[4] == "1", (uint32_t)std::stoul(cols[5]), (uint32_t)std::stoul(cols[6]),
              (uint32_t)std::stoul(cols[7]), cols[8], cols[9]};
      kname_to_id[d.name] = d.id;
      kdecls.push_back(std::move(d));
    }
  }
  uint32_t nd = (uint32_t)kdecls.size();

  // Edges
  FILE* efp = std::fopen(argv[5], "rb");
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
  std::vector<int32_t> kdecl_to_sdecl(nd, -1);
  std::vector<int32_t> kdecl_to_smod(nd, -1);
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
              for (uint32_t sdid : it->second) {
                if (sdecls[sdid].mod_idx == mid) { kdecl_to_sdecl[i] = (int32_t)sdid; break; }
              }
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
        uint32_t sdid = it->second[0];
        kdecl_to_sdecl[i] = (int32_t)sdid;
        kdecl_to_smod[i] = (int32_t)sdecls[sdid].mod_idx;
        break;
      }
      size_t dot = cur.rfind('.');
      if (dot == std::string::npos) break;
      cur.resize(dot);
    }
  }

  // Assign an exclusive source-LOC weight to each kdecl (splitting a source decl's lines onto its primary kdecl
  // so sum over kdecls == exact source decl lines without double counting ._proof_1 / .eq_1 auxiliaries!)
  std::vector<double> kdecl_loc(nd, 0.0);
  {
    std::vector<uint32_t> sdecl_kcount(sdecls.size(), 0);
    for (uint32_t i = 0; i < nd; i++) {
      if (kdecl_to_sdecl[i] >= 0) sdecl_kcount[kdecl_to_sdecl[i]]++;
    }
    for (uint32_t i = 0; i < nd; i++) {
      int32_t sd = kdecl_to_sdecl[i];
      if (sd >= 0 && sdecl_kcount[sd] > 0) {
        kdecl_loc[i] = (double)sdecls[sd].code_lines_est() / (double)sdecl_kcount[sd];
      }
    }
  }

  // Check Def CSE (exact same (type_ie, val_ie) for kind == 'd') + Prop CSE (exact same type_ie for kind == 't')!
  std::unordered_map<uint64_t, uint32_t> first_def;
  std::unordered_map<uint32_t, uint32_t> first_thm;
  std::unordered_map<uint32_t, uint32_t> redirect;
  size_t def_cse_cnt = 0;
  for (uint32_t i = 0; i < nd; i++) {
    if (kdecls[i].kind == 'd') {
      uint64_t key = ((uint64_t)kdecls[i].type_ie << 32) | kdecls[i].val_ie;
      auto [it, ins] = first_def.emplace(key, i);
      if (!ins) {
        redirect[i] = it->second;
        def_cse_cnt++;
      }
    } else if (kdecls[i].kind == 't') {
      auto [it, ins] = first_thm.emplace(kdecls[i].type_ie, i);
      if (!ins) {
        redirect[i] = it->second;
      }
    }
  }
  std::cout << "Exact Def CSE (same type_ie + val_ie) duplicates: " << def_cse_cnt << "\n";

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

  // Build compact live graph from UpperTheory.FinalTheorems.riemannHypothesis!
  std::vector<int> kid_to_gid(nd, -1);
  std::vector<uint32_t> gid_to_kid;
  std::vector<std::vector<int>> adj;

  auto get_gid = [&](uint32_t kid) {
    if (kid_to_gid[kid] == -1) {
      kid_to_gid[kid] = (int)gid_to_kid.size();
      gid_to_kid.push_back(kid);
      adj.emplace_back();
    }
    return kid_to_gid[kid];
  };

  get_gid(root_kid);
  for (size_t qi = 0; qi < gid_to_kid.size(); qi++) {
    uint32_t u_kid = gid_to_kid[qi];
    std::unordered_set<int> seen_out;
    for (uint32_t raw_v : type_deps[u_kid]) {
      uint32_t v_kid = resolve(raw_v);
      if (v_kid == u_kid) continue;
      int vg = get_gid(v_kid);
      if (seen_out.insert(vg).second) adj[qi].push_back(vg);
    }
    for (uint32_t raw_v : val_deps[u_kid]) {
      uint32_t v_kid = resolve(raw_v);
      if (v_kid == u_kid) continue;
      int vg = get_gid(v_kid);
      if (seen_out.insert(vg).second) adj[qi].push_back(vg);
    }
  }

  int N = (int)gid_to_kid.size();
  std::cout << "Compact live graph rooted at UpperTheory.FinalTheorems.riemannHypothesis: N=" << N << " nodes.\n";

  // Count live source modules & declarations for this graph
  {
    std::vector<uint8_t> smod_live(smods.size(), 0), sdecl_live(sdecls.size(), 0);
    for (uint32_t kid : gid_to_kid) {
      if (kdecl_to_smod[kid] >= 0) smod_live[kdecl_to_smod[kid]] = 1;
      if (kdecl_to_sdecl[kid] >= 0) {
        for (uint32_t sdid : name_to_sdecls[sdecls[kdecl_to_sdecl[kid]].full_name]) {
          sdecl_live[sdid] = 1;
          smod_live[sdecls[sdid].mod_idx] = 1;
        }
      }
    }
    size_t mc = 0, dc = 0;
    uint64_t dl = 0;
    for (size_t m = 0; m < smods.size(); m++) if (smod_live[m]) mc++;
    for (size_t d = 0; d < sdecls.size(); d++) if (sdecl_live[d]) { dc++; dl += sdecls[d].code_lines_est(); }
    std::cout << "After Def+Prop CSE from MainConclusion.riemannHypothesis: "
              << mc << " modules (" << (100.0 * mc / smods.size()) << "%), "
              << dc << " source decls (" << (100.0 * dc / sdecls.size()) << "%), "
              << dl << " decl lines (" << (100.0 * dl / 17374215.0) << "% of raw repo).\n";
  }

  // Run Lengauer-Tarjan Dominator Tree!
  std::cout << "Running Lengauer-Tarjan Dominator Tree on " << N << " nodes...\n";
  DominatorTree dt(N);
  dt.build(0, adj);

  // Build dominator tree children & accumulate subtree stats bottom-up!
  std::vector<std::vector<int>> dom_children(N);
  std::vector<int> dom_depth(N, 0);
  for (int i = 1; i < dt.timer; i++) {
    int u = dt.rev_dfn[i];
    int p = dt.idom[u];
    dom_children[p].push_back(u);
    dom_depth[u] = dom_depth[p] + 1;
  }

  std::vector<double> sub_loc(N, 0.0);
  std::vector<uint64_t> sub_expr_nodes(N, 0);
  std::vector<uint32_t> sub_proj_decls(N, 0);

  for (int i = dt.timer - 1; i >= 0; i--) {
    int u = dt.rev_dfn[i];
    uint32_t kid = gid_to_kid[u];
    sub_loc[u] += kdecl_loc[kid];
    if (kdecl_to_smod[kid] >= 0) {
      sub_expr_nodes[u] += kdecls[kid].own_nodes;
      sub_proj_decls[u] += 1;
    }
    if (u != 0) {
      int p = dt.idom[u];
      sub_loc[p] += sub_loc[u];
      sub_expr_nodes[p] += sub_expr_nodes[u];
      sub_proj_decls[p] += sub_proj_decls[u];
    }
  }

  // Sort dominator tree children by sub_loc descending
  for (int u = 0; u < N; u++) {
    std::sort(dom_children[u].begin(), dom_children[u].end(), [&](int a, int b) {
      return sub_loc[a] > sub_loc[b];
    });
  }

  // Print top milestone choke-points (nodes with sub_loc >= 15,000 LOC or depth <= 4 with sub_loc >= 2,000)!
  // Note: along a linear 1-child chain u -> v where sub_loc[v] > 0.95 * sub_loc[u], mark whether u is a chain wrapper or true branch!
  std::cout << "\n=== DOMINATOR CHOKE-POINT TREE (sub_loc >= 25,000 LOC) ===\n";
  std::function<void(int, int)> print_tree = [&](int u, int indent) {
    uint32_t kid = gid_to_kid[u];
    std::string mname = (kdecl_to_smod[kid] >= 0) ? smods[kdecl_to_smod[kid]].name : "[Mathlib/Core]";
    int nbig = 0;
    double children_sum = 0;
    for (int ch : dom_children[u]) {
      if (sub_loc[ch] >= 25000.0) nbig++;
      children_sum += sub_loc[ch];
    }
    double big_children_sum = 0;
    for (int ch : dom_children[u]) if (sub_loc[ch] >= 25000.0) big_children_sum += sub_loc[ch];
    double unbranched_mass = sub_loc[u] - big_children_sum;

    std::cout << std::string(indent * 2, ' ')
              << "[d=" << dom_depth[u] << "] " << (uint64_t)sub_loc[u] << " LOC ("
              << sub_proj_decls[u] << " k-decls, fanout=" << dom_children[u].size()
              << ", direct_fan_mass=" << (uint64_t)unbranched_mass << " LOC) | "
              << kdecls[kid].kind << " | " << kdecls[kid].name << "  [" << mname << "]\n";
    for (int ch : dom_children[u]) {
      if (sub_loc[ch] >= 25000.0) {
        print_tree(ch, indent + 1);
      }
    }
  };
  print_tree(0, 0);

  // Also dump top 300 dominator nodes by sub_loc to out_dom.tsv for Blueprint & Interactive Explorer!
  std::vector<int> order;
  for (int i = 0; i < dt.timer; i++) {
    int u = dt.rev_dfn[i];
    if (sub_loc[u] >= 3000.0) order.push_back(u);
  }
  std::sort(order.begin(), order.end(), [&](int a, int b) { return sub_loc[a] > sub_loc[b]; });

  std::ofstream out(argv[6]);
  out << "gid\tidom_gid\tdepth\tsub_loc\tsub_kdecls\tsub_expr_nodes\tnum_dom_children\tkind\tname\tmodule\tstart_line\tend_line\n";
  for (int u : order) {
    uint32_t kid = gid_to_kid[u];
    std::string mname = (kdecl_to_smod[kid] >= 0) ? smods[kdecl_to_smod[kid]].name : "[Mathlib/Core]";
    int sl = 0, el = 0;
    if (kdecl_to_sdecl[kid] >= 0) {
      sl = sdecls[kdecl_to_sdecl[kid]].start_line;
      el = sdecls[kdecl_to_sdecl[kid]].end_line;
    }
    out << u << '\t' << dt.idom[u] << '\t' << dom_depth[u] << '\t'
        << (uint64_t)sub_loc[u] << '\t' << sub_proj_decls[u] << '\t' << sub_expr_nodes[u] << '\t'
        << dom_children[u].size() << '\t' << kdecls[kid].kind << '\t'
        << kdecls[kid].name << '\t' << mname << '\t' << sl << '\t' << el << '\n';
  }
  std::cerr << "Wrote " << order.size() << " dominator nodes (>=3k LOC) to " << argv[6] << "\n";
  return 0;
}
