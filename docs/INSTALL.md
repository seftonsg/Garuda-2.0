# Installation & Setup

## Dependencies
- [Coq](https://coq.inria.fr)
- [Emacs](https://www.gnu.org/software/emacs/)
  - [Proof General](https://proofgeneral.github.io/)
- [Haskell](https://www.haskell.org)

To install Coq, Emacs, and Haskell, run:
```
sudo apt-get install coq emacs ghc
```
## Generating the Makefile
Make sure .coqdeps.d is defined by running coqdep. 

Then run coq_makefile.
```
coqdep * > .coqdeps.d; \
coq_makefile *.v -o Makefile
```

