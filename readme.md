# Completion

## Installation

1. Get toma(v0.7+PARSABLE) from [here](https://github.com/jajimajp/toma.git) and build it.

```bash
git clone https://github.com/jajimajp/toma.git
cd toma
make
```

For more information, see https://github.com/jajimajp/toma

2. Add your toma executable to $PATH.

```bash
export PATH="<your/path/to/toma>:$PATH"
```

```bash
$ toma -h | head -n1
toma version 0.7+PARSABLE
```

3. Clone this repository and install.

```bash
git clone https://github.com/jajimajp/coq-completion.git
cd coq-completion
make && make install
```

## How to run

You can find a lot of example Coq files in ./examples.

```bash
coqc examples/commonoid.v
```
