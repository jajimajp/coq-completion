# Completion

## Installation

1. Install dependencies:

- GNU/Make
- Glasgow Haskell Compiler 9.2.5 (or higher)
- Z3 version 4.8.12 (or higher)
- opam version 2.1.0 (or higher)
- coq 8.20.0

1. Build toma(v0.7+PARSABLE) in [./toma](./toma)

```bash
cd toma
make
```

For more information, see https://github.com/jajimajp/toma

2. Add your toma executable to $PATH

```bash
export PATH="<your/path/to/toma>:$PATH"
```

```bash
$ toma -h | head -n1
toma version 0.7+PARSABLE
```

3. Build and install this plugin

```bash
cd coq-completion
```

To install opam package dependencies, run:
```
opam install . --deps-only
```

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

