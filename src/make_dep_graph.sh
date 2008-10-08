#!/bin/sh
ghc -XPatternGuards --make coqdeps_as_dot.hs &&
  coqdep -I . *.v | ./coqdeps_as_dot | dot -Nfontsize=12 -Tpng > dep_graph.png

# We can't just use runhaskell, because it outputs readline crap that dot chokes on...
