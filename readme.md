# Completion

## Installation

0. Install dependencies:

- GNU/Make
- Glasgow Haskell Compiler 9.2.5 (or higher) \*
- Cabal \*
- Z3 version 4.8.12 (or higher)
- opam version 2.1.0 (or higher)
- coq 8.20.0

\* [GHCup](https://www.haskell.org/ghcup/) is recommended to install GHC and Cabal. You can install GHC and Cabal by running:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

See https://www.haskell.org/ghcup/ for more information.


1. Build and install toma(v0.7+PARSABLE) in [./toma](./toma)

```bash
cd toma
cabal install
```

For more information, see https://github.com/jajimajp/toma

2. Make sure correct version of toma executable can be found in $PATH.

```bash
$ toma -h | head -n1
toma version 0.7+PARSABLE
```

If toma could not be found, please add toma executable to $PATH.

```bash
export PATH="<your/path/to/toma>":$PATH
```

3. Build and install this plugin

```bash
cd coq-completion
```

To install opam package dependencies, run:
```
opam install . --deps-only
```

Make sure to update environment variables using `eval $(opam env)` after installing opam packages because some tools such as `coq_makefile` and `coqc` are used below.

To install this plugin, run:

```
make
make install
```

## Usage

You can find an overview of how to use our plugin in (./examples/Demo.v)[./examples/Demo.v].

```bash
coqc examples/Demo.v
```

## Troubleshooting

**Toma is not recognized**

When executing coqc, coqtop, or emacs from the terminal, the terminal's PATH is used. However, when executing through other means, make sure that the following two paths are registered in your PATH:

- Toma
- Z3

For example, when opening emacs from outside the terminal, you can use `M-x setenv` to set the PATH.

**Toma cannot be built in Arch Linux**

If you are using Arch Linux and encounter an error when building toma, there have been reports that some errors can be resolved by installing `ghc-static`.
