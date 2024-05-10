# SAT Encoding of Partial Ordering Models for Graph Coloring Problems
Results and Code of "SAT Encoding of Partial Ordering Models for Graph Coloring Problems"
Usage:

Make sure there is an executable of a sat-solver using the Standard DIMACS format for SAT instances in the directory
"source/solver"

To run the script use:

    python source/main.py --instance=<Path to Coloring Instance> --model=<Model to test> --timelimit=<timelimit of SAT/ILP solver in seconds>

The coloring instance must be given in the DIMACS standard format

The Model can be one of the models from the paper:
    
    ASS-I
    POP-I
    POPH-I
    ASS-S
    POP-S
    POPH-S
    ASS-I-B
    POP-I-B
    POPH-I-B
    ASS-S-B
    POP-S-B
    POPH-S-B

The timelimit is optional, the default limit is 1 hour

