CXX ?= g++
CXXFLAGS ?= -O3 -std=c++20 -Wall -Wextra

BINS = bin/index_lean_tar bin/extract_dag bin/dominators bin/compact_repo bin/rewrite_export bin/rewrite_export_v2 bin/audit_9m bin/build_skinny_tar bin/build_bundled_tar

all: $(BINS)

bin/%: tools/%.cpp
	@mkdir -p bin
	$(CXX) $(CXXFLAGS) $< -o $@

clean:
	rm -rf bin
