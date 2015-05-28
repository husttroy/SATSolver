# SATSolver
--The directory primitives/ defines the sat primitives you need to implement.
All your work should be done in this directory, and you will only submit this
directory

--The directory sat_solver/ includes C code to build a sat solver. When you
finish implementing the sat primitives, you can immediately build a sat solver
by linking the static C library libsat.a with the code in this directory (you
will create libsat.a in the directory primitives/). Then you can test your
functions on the sat solver.

--The directory c2D_code/ includes the code for c2D, which is a knowledge
compiler/model counter. When you finish implementing the sat primitives, you can
immediately use the c2D by linking the static C library libsat.a with the code
in this directory (you will create libsat.a in the directory primitives). For
the class-wide competition, we will use the c2D linked with your implementation
of libsat.a. Do not change any piece of code in this directory while testing
your implementation. That is, your implementation should be working without
making any changes to the current directory (as this is how we will test it).

--The directory benchmarks/ contains some cnf instances that will be used during
the competition. You can test your implementation on these instances.

--The directory executables/ contains executables we obtained by linking our own
sat library with the provided code
