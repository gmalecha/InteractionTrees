# Interaction Trees

Formalization of the Interaction Tree Datatype in Coq

**NOTE: This library is currently in a pre-alpha stage, the interfaces currently exposed by the repository are undergoing a great deal of exploration and there will likely be substantial changes in the future. Backwards compatibility will not be a priority as this library evolves, so dependencies should be wary of this.**

## Dependencies

- [coq-paco](https://github.com/snu-sf/paco)
- [coq-ext-lib](https://github.com/coq-ext-lib/coq-ext-lib)

## Build instructions

Choose one of the following methods.

### 1. Build everything locally

Run `setup.sh` from the root directory to download dependencies (in `lib/`) and build the project.

#### One-liner from scratch

```
git clone https://github.com/DeepSpec/InteractionTrees.git && cd InteractionTrees && ./setup.sh
```

### 2. Install dependencies with OPAM

```
opam install coq-paco coq-ext-lib
```

Now you can build the project with:

```
make
```

### 3. Use dependencies installed elsewhere

If you would like to use local versions of some of the dependencies, create a
`_CoqPath` file with the paths to the libraries that you would like to include.
For example,

```
-Q path/to/paco/src Paco
```

Now you can build the project with:

```
make
```
