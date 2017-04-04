# tr-performance

A thrown together tool for some rough measurements on some Typed Racket typecheck times.

Note: requires `require-typed-check` to be installed on the control and test racket installs

Usage details:

```
racket main.rkt [ <option> ... ] <control> <test>
 where <option> is one of
  -v, --verbose : Build with verbose messages
  -p, --plot : Plot results
* -t <target>, --target <target> : Only build a single target
* -i <i>, --iters <i> : How many iterations?
  --help, -h : Show this help
  -- : Do not treat any remaining argument as a switch (at this level)
 * Asterisks indicate options allowed multiple times.
 Multiple single-letter switches can be combined after one `-'; for
  example: `-h-' is the same as `-h --'
```

and where `<control>` is the `bin` directory for the "control" Racket install and `<test>` is the `bin` directory for the "test" Racket install.

Example usage and output:

```
racket main.rkt -t new-metrics -v /Users/pnwamk/Repos/plt/6.8/bin /Users/pnwamk/Repos/plt/dev/racket/bin
building new-metrics..........
/Users/pnwamk/Repos/plt/6.8/bin/raco make new-metrics:
  times (3.12 3.04 3.02 3.03 3.05 3.08 3.06 3.05 3.04 3.1)
  mean 3.06
  stddev 0.03
done with new-metrics
building new-metrics..........
/Users/pnwamk/Repos/plt/dev/racket/bin/raco make new-metrics:
  times (3.26 3.24 3.2 3.24 3.22 3.24 3.23 3.23 3.23 3.25)
  mean 3.23
  stddev 0.02
done with new-metrics

results:
new-metrics: 5.56% slower (3.06s to 3.23s)
```
  


