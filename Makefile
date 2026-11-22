CXX ?= g++
CXXFLAGS ?= -O3 -std=c++20 -Wall -Wextra

BINS = bin/index_lean_tar bin/extract_dag bin/dominators bin/compact_repo bin/rewrite_export

all: $(BINS)

bin/%: tools/%.cpp
	@mkdir -p bin
	$(CXX) $(CXXFLAGS) $< -o $@

clean:
	rm -rf bin
