# Using

## Printing JBir HTML

Just use `$ ./main.sh print-jbir`:

```bash
Print out the JBir representation of java bytecode.

  main.byte print-jbir

=== flags ===

  -c class     file to print.
  [-m method]  name in class file to target.
  [-o output]  folder to write html to.
  [-help]      print this help text and exit
               (alias: -?)
```

Here's an example:

```bash
javac -g examples/climb-stairs/ClimbStairs.java
./main.sh print -c examples/climb-stairs/ClimbStairs.class
```

## Printing a Program Graph

```
Print out dot file of many classes and methods.

  main.byte print-graph 

=== flags ===

  [-c class]   file to analyze (put before method name).
  [-m method]  name in classfile to target.
  [-o output]  folder to write dot data to.
  [-help]      print this help text and exit

```

Here's an example:

```
javac -g examples/climb-stairs/ClimbStairs.java
./main.sh print-graph -c ./examples/climb-stairs/ClimbStairs.class -m 'climbStairs1(I)I' \
                      -c ./examples/climb-stairs/ClimbStairs.class -m 'climbStairs0(I)I'
dot -Tsvg -O dot-out/*.dot
```

And here's a sample output:

![graph of first climbstairs function][climbstairs_graph]

## A Note about Methods '-m'

You can specify a method to target in the command line, the format is
`method_name(args_list)ret_val` where the types are specified using the
JVM codes for types:

Character | Type
--- | ---
`B` | Byte
`C` | Char
`D` | Double
`F` | Float
`I` | Int
`J` | Long
`S` | Short
`V` | Void
`Z` | Boolean
`[` | Array of the thing following the bracket (Array of ints is `[I`).
`L<class name>;` | full path of class name.

So the main method signature `void main(String[] args)` will be represented
as `main([Ljava.lang.String;)V`.

# Contributing

First install OPAM: https://opam.ocaml.org/doc/Install.html
   
```
# init opam
opam init -y

# configure env vars
eval $(opam config env)
echo 'eval $(opam config env)' >> ~/.bashrc

# switch to compiler 4.03.0
opam switch 4.03.0

# This can get complicated, follow all the prompts and install the deps it says.
opam install -y oasis core sawja ocamlgraph ppx_deriving

git clone 'https://bitbucket.org/wrharris/sim-itps.git'
cd sim-itps
git checkout sawja

make
```

Then install Java OpenJDK 7.
Check the printing-jbir example to make sure everything's OK!

## Tips

### Documentation Generation

```
opam install odoc odig ocaml-manual
odig odoc
odig doc
```

### Autocomplete

Make sure to install `merlin` along with your editor's autocomplete plugin.

```
opam install -y merlin
```


[climbstairs_graph]: https://bytebucket.org/wrharris/sim-itps/raw/b4aee28270087d3399bdecd30a3921edb316a7ad/examples/climb-stairs/ClimbStairs-climbStairs0.dot.png?token=5a097d5463fab8d91a6f64f52e6121e3d7eeb060
