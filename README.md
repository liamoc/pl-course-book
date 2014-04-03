# About
Together with UNSW professor
[Gabriele Keller](http://www.cse.unsw.edu.au/~keller/), I have taught a
[third year undergraduate course](https://www.openlearning.com/unsw/courses/COMP3161)
on programming languages (mostly on static semantics, types and operational
semantics) for about 4 years. For various reasons, our course does not follow
the widely used textbooks in this area (namely Pierce's TAPL and Harper's PFPL),
mostly because they are targeted at a slightly more mathematically mature
audience. Recently, some lecturers from other universities expressed an interest
in running a course similar to ours, which prompted us to dig up our lecture
notes and materials for the course, and begin this project. This book is therefore 
based on lecture notes that Gabi and I prepared over the last few years for the UNSW
course, but we invite contributions from anyone. Some of the lecture notes for
the first chapter made use of material from Frank Pfenning and Bob Harper, so
some attribution also belongs to them.

This book is currently in a very incomplete state. We don't recommend using it
just yet. Until then, the [competition](www.cs.cmu.edu/~rwh/plbook/book.pdf)
comes [very highly recommended](http://www.cis.upenn.edu/~bcpierce/tapl/).

Patches and contributions are welcome from absolutely anyone who feels they
can contribute. 

# Building

You will need a reasonably recent TeXLive installation including `latexmk`. You
can use the makefile to generate a pdf, either of the whole book, or just of a
single chapter. For example:

    make # generates the whole book as main.pdf

	make ch1-prelims # generates a pdf of just one chapter as ch1-prelims.pdf
	

# License

![CC-BY-SA](http://mirrors.creativecommons.org/presskit/buttons/88x31/svg/by-sa.svg)

This work is licensed under the Creative Commons Attribution-ShareAlike 4.0
International License. To view a copy of this license, visit
http://creativecommons.org/licenses/by-sa/4.0/.




