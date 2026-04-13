CADICALBUILD=/Users/huguangyu/coding_env/pono-llm4assert/deps/smt-switch/deps/boolector/deps/cadical/build
all:
	make -C "$(CADICALBUILD)"
clean:
	@if [ -d "$(CADICALBUILD)" ]; \
	then \
	  if [ -f "$(CADICALBUILD)"/makefile ]; \
	  then \
	     touch "$(CADICALBUILD)"/build.hpp; \
	     touch "$(CADICALBUILD)"/dependencies; \
	     make -C "$(CADICALBUILD)" clean; \
	  fi; \
	  rm -rf "$(CADICALBUILD)"; \
	fi
	rm -f "/Users/huguangyu/coding_env/pono-llm4assert/deps/smt-switch/deps/boolector/deps/cadical/makefile"
test:
	make -j1 -C "$(CADICALBUILD)" test
cadical:
	make -j1 -C "$(CADICALBUILD)" cadical
mobical:
	make -j1 -C "$(CADICALBUILD)" mobical
update:
	make -j1 -C "$(CADICALBUILD)" update
.PHONY: all cadical clean mobical test update
