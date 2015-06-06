#include <stdio.h>
#include "primitive/sat_api.h"





Lit* get_free_literal(SatState* sat_state);

Clause* sat_aux(SatState* sat_state);

BOOLEAN sat(SatState* sat_state);

void print_CNF (SatState* sat);

int main (int argc, char* argv[]) {

    SatState* sat_state = sat_state_new("/Users/yuan/Desktop/TestSAT/benchmarks/test.cnf");

    print_CNF(sat_state);

    if(sat(sat_state)){
        printf("SAT\n");
    } else {
        printf("UNSAT\n");
    }

    sat_state_free(sat_state);

    return 0;

}




Lit* get_free_literal(SatState* sat_state) {
    c2dSize var_count = sat_var_count(sat_state);
    for(c2dSize i=0; i<var_count; i++) { //go over variables
        Var* var  = sat_index2var(i+1,sat_state); //note index is i+1, not i
        Lit* plit = sat_pos_literal(var);
        Lit* nlit = sat_neg_literal(var);
        if(!sat_implied_literal(plit) && !sat_implied_literal(nlit)) return plit;
    }
    return NULL; //all literals are implied
}


//if sat state is shown to be satisfiable, it returns NULL
//otherwise, a clause must be learned and it is returned
Clause* sat_aux(SatState* sat_state) {
    Lit* lit = get_free_literal(sat_state);
    if(lit == NULL) return NULL; //all literals are implied

    Clause* learned = sat_decide_literal(lit,sat_state);
    if(learned == NULL) learned = sat_aux(sat_state);
    sat_undo_decide_literal(sat_state);

    if(learned != NULL) { //there is a conflict
        if(sat_at_assertion_level(learned,sat_state)) {
            learned = sat_assert_clause(learned,sat_state);
            if(learned == NULL){
                return sat_aux(sat_state);
            } //try again
            else {
                return learned;
            } //new clause learned, backtrack

        }
        else {
            return learned;
        } //backtrack (still conflict)

    }
    return NULL; //satisfiable
}

BOOLEAN sat(SatState* sat_state) {
    BOOLEAN ret = 0;
    if(sat_unit_resolution(sat_state)) {
        ret = (sat_aux(sat_state)==  NULL? 1 : 0);
    }
    sat_undo_unit_resolution(sat_state); // everything goes back to the initial state
    return ret;
}








