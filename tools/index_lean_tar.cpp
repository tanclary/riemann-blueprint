#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

struct ScopeItem {
  std::string seg;
  bool is_ns;  // true = namespace, false = section
};

static bool is_ident_char(unsigned char c) {
  return std::isalnum(c) || c == '_' || c == '\'' || c >= 0x80 || c == '?' || c == '!';
}

static std::vector<std::string> split_dots(const std::string& s) {
  std::vector<std::string> out;
  size_t start = 0;
  while (start < s.size()) {
    size_t dot = s.find('.', start);
    if (dot == std::string::npos) {
      out.push_back(s.substr(start));
      break;
    }
    out.push_back(s.substr(start, dot - start));
    start = dot + 1;
  }
  return out;
}

struct Token {
  std::string text;
  int line;
  int col;
};

static void tokenize_lean(const char* data, size_t len, std::vector<Token>& toks, int& total_lines, int& code_lines) {
  toks.clear();
  int line = 1, col = 1;
  int block_depth = 0;
  bool line_has_code = false;
  code_lines = 0;

  size_t i = 0;
  while (i < len) {
    unsigned char c = (unsigned char)data[i];
    if (c == '\n') {
      if (line_has_code) code_lines++;
      line_has_code = false;
      line++;
      col = 1;
      i++;
      continue;
    }
    if (block_depth > 0) {
      if (c == '/' && i + 1 < len && data[i + 1] == '-') {
        block_depth++;
        i += 2;
        col += 2;
      } else if (c == '-' && i + 1 < len && data[i + 1] == '/') {
        block_depth--;
        i += 2;
        col += 2;
      } else {
        i++;
        col++;
      }
      continue;
    }
    // Check comments
    if (c == '/' && i + 1 < len && data[i + 1] == '-') {
      block_depth = 1;
      i += 2;
      col += 2;
      continue;
    }
    if (c == '-' && i + 1 < len && data[i + 1] == '-') {
      // skip to end of line
      while (i < len && data[i] != '\n') i++;
      continue;
    }
    if (std::isspace(c)) {
      i++;
      col++;
      continue;
    }
    line_has_code = true;
    // String literal
    if (c == '"') {
      int sc = col;
      i++;
      col++;
      while (i < len && data[i] != '"') {
        if (data[i] == '\\' && i + 1 < len) {
          if (data[i + 1] == '\n') { line++; col = 1; }
          else col += 2;
          i += 2;
        } else {
          if (data[i] == '\n') {
            if (line_has_code) code_lines++;
            line_has_code = true;
            line++;
            col = 1;
          } else {
            col++;
          }
          i++;
        }
      }
      if (i < len) { i++; col++; }
      toks.push_back({"\"\"", line, sc});
      continue;
    }
    // Guillemet identifier «...» (UTF-8 \xc2\xab ... \xc2\xbb) or regular identifier/dotted
    if (is_ident_char(c) || c == '.') {
      int sc = col;
      int sl = line;
      size_t start = i;
      while (i < len && (is_ident_char((unsigned char)data[i]) || data[i] == '.')) {
        i++;
        col++;
      }
      toks.push_back({std::string(data + start, i - start), sl, sc});
      continue;
    }
    // Punctuation token (single char or [ / ])
    int sc = col;
    toks.push_back({std::string(1, (char)c), line, sc});
    i++;
    col++;
  }
  if (line_has_code) code_lines++;
  total_lines = (len == 0) ? 0 : (data[len - 1] == '\n' ? line - 1 : line);
}

static bool is_modifier(const std::string& s) {
  return s == "private" || s == "protected" || s == "noncomputable" ||
         s == "unsafe" || s == "partial" || s == "scoped" || s == "local";
}

static bool is_decl_kw(const std::string& s) {
  return s == "theorem" || s == "lemma" || s == "def" || s == "abbrev" ||
         s == "structure" || s == "inductive" || s == "class" ||
         s == "instance" || s == "opaque" || s == "axiom";
}

int main(int argc, char** argv) {
  if (argc < 4) {
    std::cerr << "Usage: index_lean_tar <lean.tar> <modules.tsv> <decls.tsv>\n";
    return 1;
  }
  FILE* fp = std::fopen(argv[1], "rb");
  if (!fp) { std::perror("fopen tar"); return 1; }
  std::ofstream mod_out(argv[2]);
  std::ofstream decl_out(argv[3]);

  mod_out << "module\ttotal_lines\tcode_lines\tnum_imports\tnum_decls\thas_syntax_or_attr\timports\n";
  decl_out << "module\tkind\tis_private\tfull_name\tstart_line\tend_line\n";

  unsigned char hdr[512];
  std::vector<char> buf;
  std::vector<Token> toks;
  std::string pending_longlink;

  size_t files_seen = 0;
  size_t decls_seen = 0;

  while (std::fread(hdr, 1, 512, fp) == 512) {
    bool all_zero = true;
    for (int i = 0; i < 512; i++) if (hdr[i] != 0) { all_zero = false; break; }
    if (all_zero) continue;

    // Parse octal size at [124..136)
    size_t sz = 0;
    for (int i = 124; i < 136 && hdr[i]; i++) {
      if (hdr[i] >= '0' && hdr[i] <= '7') sz = (sz << 3) + (hdr[i] - '0');
    }
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
        // Parse PAX records: "<len> <key>=<val>\n"
        size_t pos = 0;
        while (pos < sz) {
          size_t sp = pos;
          while (sp < sz && buf[sp] >= '0' && buf[sp] <= '9') sp++;
          if (sp == pos || sp >= sz || buf[sp] != ' ') break;
          size_t rec_len = std::strtoul(std::string(buf.data() + pos, sp - pos).c_str(), nullptr, 10);
          if (rec_len == 0 || pos + rec_len > sz) break;
          std::string rec(buf.data() + sp + 1, pos + rec_len - (sp + 1) - 1);  // strip trailing \n
          if (rec.compare(0, 5, "path=") == 0) {
            pending_longlink = rec.substr(5);
          }
          pos += rec_len;
        }
      }
      continue;
    }
    if (typeflag != '0' && typeflag != '\0') {
      if (padded > 0) std::fseek(fp, (long)padded, SEEK_CUR);
      continue;
    }

    buf.resize(padded);
    if (padded > 0 && std::fread(buf.data(), 1, padded, fp) != padded) break;

    const std::string pfx = "lean/src/";
    const std::string sfx = ".lean";
    if (name.size() <= pfx.size() + sfx.size() ||
        name.compare(0, pfx.size(), pfx) != 0 ||
        name.compare(name.size() - sfx.size(), sfx.size(), sfx) != 0) {
      continue;
    }

    std::string mod = name.substr(pfx.size(), name.size() - pfx.size() - sfx.size());
    for (char& ch : mod) if (ch == '/') ch = '.';

    int total_lines = 0, code_lines = 0;
    tokenize_lean(buf.data(), sz, toks, total_lines, code_lines);

    std::vector<std::string> imports;
    std::vector<ScopeItem> scopes;
    bool has_syntax_or_attr = false;

    struct DeclRec {
      std::string kind;
      bool is_priv;
      std::string full_name;
      int start_line;
      int end_line;
    };
    std::vector<DeclRec> decls;

    auto current_ns = [&]() {
      std::string ns;
      for (const auto& s : scopes) {
        if (s.is_ns) {
          if (!ns.empty()) ns += '.';
          ns += s.seg;
        }
      }
      return ns;
    };

    for (size_t idx = 0; idx < toks.size(); idx++) {
      const Token& t = toks[idx];
      // Only consider top-of-statement constructs at col == 1 (or col <= 3)
      if (t.col == 1 && t.text == "import" && idx + 1 < toks.size()) {
        imports.push_back(toks[idx + 1].text);
        idx++;
        continue;
      }
      if (t.col == 1 && t.text == "namespace" && idx + 1 < toks.size()) {
        if (!decls.empty() && decls.back().end_line == 0) decls.back().end_line = t.line - 1;
        for (const auto& seg : split_dots(toks[idx + 1].text)) {
          if (!seg.empty()) scopes.push_back({seg, true});
        }
        idx++;
        continue;
      }
      if (t.col == 1 && t.text == "section") {
        if (!decls.empty() && decls.back().end_line == 0) decls.back().end_line = t.line - 1;
        if (idx + 1 < toks.size() && toks[idx + 1].line == t.line) {
          for (const auto& seg : split_dots(toks[idx + 1].text)) {
            if (!seg.empty()) scopes.push_back({seg, false});
          }
          idx++;
        } else {
          scopes.push_back({"", false});
        }
        continue;
      }
      if (t.col == 1 && t.text == "end") {
        if (!decls.empty() && decls.back().end_line == 0) decls.back().end_line = t.line - 1;
        if (idx + 1 < toks.size() && toks[idx + 1].line == t.line) {
          auto segs = split_dots(toks[idx + 1].text);
          for (size_t k = 0; k < segs.size() && !scopes.empty(); k++) scopes.pop_back();
          idx++;
        } else {
          if (!scopes.empty()) scopes.pop_back();
        }
        continue;
      }
      if (t.col <= 4) {
        if (t.text == "macro" || t.text == "elab" || t.text == "syntax" ||
            t.text == "notation" || t.text == "infix" || t.text == "infixl" ||
            t.text == "infixr" || t.text == "prefix" || t.text == "postfix" ||
            t.text == "attribute") {
          has_syntax_or_attr = true;
        }
        // Check @[...] attributes or modifiers followed by decl_kw
        size_t j = idx;
        int start_ln = t.line;
        bool is_priv = false;
        if (toks[j].text == "@") {
          has_syntax_or_attr = true;
          // skip @[ ... ]
          if (j + 1 < toks.size() && toks[j + 1].text == "[") {
            int br = 1;
            j += 2;
            while (j < toks.size() && br > 0) {
              if (toks[j].text == "[") br++;
              else if (toks[j].text == "]") br--;
              j++;
            }
          }
        }
        while (j < toks.size() && is_modifier(toks[j].text)) {
          if (toks[j].text == "private") is_priv = true;
          j++;
        }
        if (j < toks.size() && is_decl_kw(toks[j].text) && (j == idx || toks[j].col <= 40)) {
          if (!decls.empty() && decls.back().end_line == 0) {
            decls.back().end_line = std::max(decls.back().start_line, start_ln - 1);
          }
          std::string kw = toks[j].text;
          std::string dname;
          if (kw == "class" && j + 1 < toks.size() && toks[j + 1].text == "inductive") {
            j++;
          }
          if (j + 1 < toks.size()) {
            const std::string& cand = toks[j + 1].text;
            if (cand != ":" && cand != "(" && cand != "{" && cand != "[" && cand != "⦃" && cand != "where" && cand != ":=") {
              dname = cand;
            } else {
              dname = "<anon_inst>";
            }
          }
          std::string full;
          if (dname == "<anon_inst>") {
            std::string ns = current_ns();
            full = ns.empty() ? "<anon_inst>" : (ns + ".<anon_inst>");
          } else if (dname.compare(0, 7, "_root_.") == 0) {
            full = dname.substr(7);
          } else {
            std::string ns = current_ns();
            full = ns.empty() ? dname : (ns + "." + dname);
          }
          decls.push_back({kw, is_priv, full, start_ln, 0});
          idx = j;
        }
      }
    }
    if (!decls.empty() && decls.back().end_line == 0) {
      decls.back().end_line = total_lines;
    }

    mod_out << mod << '\t' << total_lines << '\t' << code_lines << '\t'
            << imports.size() << '\t' << decls.size() << '\t'
            << (has_syntax_or_attr ? 1 : 0) << '\t';
    for (size_t k = 0; k < imports.size(); k++) {
      if (k) mod_out << ',';
      mod_out << imports[k];
    }
    mod_out << '\n';

    for (const auto& d : decls) {
      decl_out << mod << '\t' << d.kind << '\t' << (d.is_priv ? 1 : 0) << '\t'
               << d.full_name << '\t' << d.start_line << '\t' << d.end_line << '\n';
    }
    files_seen++;
    decls_seen += decls.size();
  }
  std::fclose(fp);
  std::cerr << "Indexed " << files_seen << " modules, " << decls_seen << " declarations.\n";
  return 0;
}
