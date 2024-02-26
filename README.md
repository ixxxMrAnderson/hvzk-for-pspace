# blic – BDD Library with Interactive Certification

`blic` is a certifying [QBF](https://en.wikipedia.org/wiki/True_quantified_Boolean_formula) solver based on [interactive certificates](https://en.wikipedia.org/wiki/IP_(complexity)) (also known as interactive proofs).

## Compile

Run `./build.sh` for a release build (optimisations enabled, warnings ignored). This will produce an executable named `solver`. You can also compile debug builds with `./build.sh debug`. See `./build.sh --help` for a full list of modes.

To compile manually (or integrate compilation into your build system of choice, note that `blic` uses a single translation-unit build. This means that you only need to compile `solver.cpp`; it includes all other files. The code is written using C++14 (e.g. for `gcc` you might want to pass `-std=c++14`). `blic` uses neither exceptions nor RTTI, so you can safely disable those (e.g. `-fno-exceptions -fno-rtti`). 

## Usage

`blic` solves QBF instances in [QDIMACS](http://www.qbflib.org/qdimacs.html) format.

    ./solver [<options>...] <instance>

For example:

    ./solver -v test/simple1_or.qdimacs
    
There are a variety of debug and visualisation options, see `./solver --help` for a full list. 

## Structure

* `solver.cpp`: Main file, implementing the CLI.
* `ffe.cpp`: Finite field arithmetic.
* `expr.cpp`: Representation of CPEs.
* `verifier.cpp`: Implementation of the Verifier side of the CPCertify protocol.
* `bdd.cpp`: BDD algorithms, with support for tracking of intermediate eBDDs and arithmetisation.
* `prover.cpp`: Uses `bdd.cpp` to implement the Prover side of the CPCertify protocol. It also implements experimental support for sending challenges over a network connection.
* `server.cpp`: Experimental support to provide a network interface responding to challenges.
* `smvparser.cpp`: Experimental support to parse SMV files.
* `lib`: Generic libraries.
* `build.sh`: Build system.
* `monkey.py`: Random testing support.

## License

`blic` is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

`blic` is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with `blic`. If not, see <https://www.gnu.org/licenses/>. 
