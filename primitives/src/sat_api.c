/*
 * sat_api.c
 *
 *  Created on: May 28, 2015
 *      Author: troy
 */

#include "sat_api.h"

/******************************************************************************
 * We explain here the functions you need to implement
 *
 * Rules:
 * --You cannot change any parts of the function signatures
 * --You can/should define auxiliary functions to help implementation
 * --You can implement the functions in different files if you wish
 * --That is, you do not need to put everything in a single file
 * --You should carefully read the descriptions and must follow each requirement
 ******************************************************************************/

/******************************************************************************
 * Variables
 ******************************************************************************/

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state) {
	Var ** var = sat_state->vars;
	return var[index - 1];
}

//returns the index of a variable
c2dSize sat_var_index(const Var* var) {
	return var->index;
}

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit) {
	return lit->var;
}

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var) {
	return var->value == -1 ? 0 : 1;
}

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
//	Clause ** clauses = var->clauses;
//	for (int i = 0; i < var->clause_num; i++) {
//		Clause * clause = clauses[i];
//		if (clause->asserted == 0)
//			return 0;
//	}
//
//	return 1;
	for(int i=0; i<sat_var_occurences(var); i++) {
	    Clause* clause = sat_clause_of_var(i,var);
	    if(!sat_subsumed_clause(clause)) return 0;
	}
	return 1;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
	return sat_state->var_num;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {
	return var->clause_num;
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {
	if (index > -1 && index < var->clause_num) {
		return var->clauses[index];
	} else {
		return NULL;
	}
}

/******************************************************************************
 * Literals
 ******************************************************************************/

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
	Lit ** lits = sat_state->lits;
	if (index > 0) {
		return lits[2 * (index - 1)];
	} else {
		return lits[2 * (-index) - 1];
	}
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
	return lit->index;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
	return var->pos;
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
	return var->neg;
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
	return sat_instantiated_var(lit->var);
}

void add_lit_to_pending(Lit* lit, SatState* sat) {
	if (sat->pending_num + 1 > sat->pending_capacity) {
		sat->pending_capacity *= 2;
		sat->pending = (Lit **) realloc(sat->pending,
				sat->pending_capacity * sizeof(Lit *));
	}

	sat->pending[sat->pending_num] = lit;
	sat->pending_num++;
	return;
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
	if (lit->index > 0) {
		lit->var->value = 1;
	} else {
		lit->var->value = 0;
	}

	// update its decision level
	lit->var->decision_level = sat_state->decision_level + 1;
	if (sat_state->decision_capacity < sat_state->decision_level) {
		sat_state->decision_capacity *= 2;
		sat_state->decisions = (Lit **) realloc(sat_state->decisions,
				sat_state->decision_capacity * sizeof(Lit *));
	}
	sat_state->decisions[sat_state->decision_level - 1] = lit;
	sat_state->decision_level++;

//	for (int i = 0; i < lit->clause_num; i++) {
//		// increment the asserted literal counter
//		Clause * c = lit->clauses[i];
//		c->asserted++;
//	}

	// add the decide literal to pending
	add_lit_to_pending(lit, sat_state);

	if (!sat_unit_resolution(sat_state)) {
		// find a contradiction
		return sat_state->asserting;
	} else {
		return NULL;
	}
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
	Lit * lit = sat_state->decisions[sat_state->decision_level - 2]; // decision sequence is empty in level 1, so the array index is actually level - 2
	sat_state->decisions[sat_state->decision_level - 2] = NULL;
	lit->var->value = -1;
	lit->var->decision_level = 0;

//	for (int i = 0; i < lit->clause_num; i++) {
//		// decrement the asserted literal counter
//		Clause * c = lit->clauses[i];
//		c->asserted--;
//	}

	sat_undo_unit_resolution(sat_state);
	sat_state->decision_level--;
	return;
}

/******************************************************************************
 * Clauses
 ******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
	Clause ** clauses = sat_state->cnf;
	return clauses[index - 1];
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {
	return clause->index;
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {
	return clause->lits;
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {
	return clause->size;
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {
//	return clause->asserted > 0;
	for(int i = 0; i < clause->size; i++){
		Lit * lit = clause->lits[i];
		if((lit->index > 0 && lit->var->value == 1) || ((lit->index < 0) && (lit->var->value == 0))){
			return 1;
		}
	}

	return 0;
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {
	return sat_state->clause_num;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {
	return sat_state->learn_num;
}

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
	// check the size of the learned clause, reallocate the array when necessary
	Clause ** learns = sat_state->learns;
	int size = sat_state->learn_num;
	int capacity = sat_state->learn_capacity;

	if (size == capacity) {
		capacity *= 2;
		learns = (Clause **) realloc(learns, capacity * sizeof(Clause *));
		sat_state->learn_capacity = capacity;
		sat_state->learns = learns;
	}

	learns[size] = clause;
	sat_state->learn_num++;

	if (!sat_unit_resolution(sat_state)) {
		// find a contradiction
		return sat_state->asserting;
	} else {
		// succeed
		return NULL;
	}
}

/******************************************************************************
 * A SatState should keep track of pretty much everything you will need to
 * condition/uncondition variables, perform unit resolution, and do clause learning
 *
 * Given an input cnf file you should construct a SatState
 *
 * This construction will depend on how you define a SatState
 * Still, you should at least do the following:
 * --read a cnf (in DIMACS format, possible with weights) from the file
 * --initialize variables (n of them)
 * --initialize literals  (2n of them)
 * --initialize clauses   (m of them)
 *
 * Once a SatState is constructed, all of the functions that work on a SatState
 * should be ready to use
 *
 * You should also write a function that frees the memory allocated by a
 * SatState (sat_state_free)
 ******************************************************************************/

// helper function, check if str starts with pre.
int startsWith(const char *pre, const char *str) {
	size_t lenpre = strlen(pre), lenstr = strlen(str);
	return lenstr < lenpre ? 0 : strncmp(pre, str, lenpre) == 0;
}

void add_clause_to_var(Var * var, Clause * clause) {
	if (var->clause_num + 1 > var->clause_capacity) {
		var->clause_capacity *= 2;
		var->clauses = (Clause **) realloc(var->clauses,
				var->clause_capacity * sizeof(Clause *));
	}

	var->clauses[var->clause_num] = clause;
	var->clause_num++;
}

void add_clause_to_lit(Lit * lit, Clause * clause) {
	if (lit->clause_num + 1 > lit->clause_capacity) {
		lit->clause_capacity *= 2;
		lit->clauses = (Clause **) realloc(lit->clauses,
				lit->clause_capacity * sizeof(Clause *));
	}

	lit->clauses[lit->clause_num] = clause;
	lit->clause_num++;
}

void add_lit_to_implies(Lit* lit, Clause * reason, SatState* sat) {
	if (sat->implies_num + 1 > sat->implies_capacity) {
		sat->implies_capacity *= 2;
		sat->implies = (Lit **) realloc(sat->implies,
				sat->implies_capacity * sizeof(Lit *));
	}

	lit->var->decision_level = sat->decision_level;
	lit->var->value = lit->index > 0 ? 1 : 0;
	lit->var->reason = reason;
	sat->implies[sat->implies_num] = lit;
	sat->implies_num++;

//	for (int i = 0; i < lit->clause_num; i++) {
//		// increment the asserted literal counter
//		Clause * c = lit->clauses[i];
//		c->asserted++;
//	}

	add_lit_to_pending(lit, sat);
}

Lit * pop_lit_from_pending(SatState * sat) {
	if (sat->pending_num == 0) {
		return NULL;
	} else {
		Lit * lit = sat->pending[0];
		// shift to left
		for (int i = 1; i < sat->pending_num; i++) {
			sat->pending[i - 1] = sat->pending[i];
		}
		sat->pending[sat->pending_num - 1] = NULL;
		sat->pending_num--;
		return lit;
	}
}

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name) {
	FILE *fp = fopen(file_name, "r");
	const size_t len = 2147483647;
	char *line = (char *) malloc(len);
	SatState* sat_state = (SatState*) malloc(sizeof(SatState));

	if (fp == NULL) {
		printf("%s",
				"Cannot read the cnf file, please check if it exists or is broken. Program Exit.");
		exit(1);
	}

	int clause_count = 0;
	while (fgets(line, len, fp) != NULL) {
		if (startsWith("0", line) || startsWith("c", line)
				|| startsWith("%", line) || startsWith("ccc", line)
				|| startsWith("cc", line) || startsWith("\n", line))
			continue; // comment line
		else if (startsWith("p", line)) {
			// problem line, tokenize it
			char * token = strtok(line, " ");
			int count = 0;
			while (token) {
				if (count == 2) {
					// read variable number
					int var_num = atoi(token);
					sat_state->var_num = var_num;
					sat_state->vars = (Var **) malloc(sizeof(Var *) * var_num);
					for (int i = 0; i < var_num; i++) {
						Var * var = (Var *) malloc(sizeof(Var));
						var->index = i + 1;
						var->pos = NULL;
						var->neg = NULL;
						var->clauses = (Clause **) malloc(
								sizeof(Clause *) * 200);
						var->clause_num = 0;
						var->clause_capacity = 200;
						var->value = -1;
						var->decision_level = 0;
						var->reason = NULL;
						var->mark = 0;
						sat_state->vars[i] = var;
					}

					sat_state->lits = (Lit **) malloc(
							sizeof(Lit *) * var_num * 2);
					sat_state->lit_num = var_num * 2;
					for (int i = 0; i < var_num; i++) {
						Lit * pos = (Lit *) malloc(sizeof(Lit));
						pos->index = i + 1;
						pos->var = sat_state->vars[i];
						pos->redundant = 0;
						pos->clauses = (Clause **) malloc(
								sizeof(Clause *) * 200);
						pos->clause_num = 0;
						pos->clause_capacity = 200;
						Lit * neg = (Lit *) malloc(sizeof(Lit));
						neg->index = -(i + 1);
						neg->var = sat_state->vars[i];
						neg->redundant = 0;
						neg->clauses = (Clause **) malloc(
								sizeof(Clause *) * 200);
						neg->clause_num = 0;
						neg->clause_capacity = 200;

						sat_state->lits[2 * i] = pos;
						sat_state->lits[2 * i + 1] = neg;
						sat_state->vars[i]->pos = pos;
						sat_state->vars[i]->neg = neg;
					}
				} else if (count == 3) {
					// read clause number
					int clause_num = atoi(token);
					sat_state->clause_num = clause_num;
					sat_state->cnf = (Clause **) malloc(
							sizeof(Clause *) * clause_num);
				}

				token = strtok(NULL, " ");
				count++;
			}

			sat_state->learns = (Clause **) malloc(sizeof(Clause *) * 200);
			sat_state->learn_num = 0;
			sat_state->learn_capacity = 200;
			sat_state->decisions = (Lit **) malloc(
					sizeof(Lit *) * sat_state->var_num);
			sat_state->decision_level = 1;
			sat_state->decision_capacity = sat_state->var_num;
			sat_state->implies = (Lit **) malloc(
					sizeof(Lit *) * sat_state->var_num);
			sat_state->implies_num = 0;
			sat_state->implies_capacity = sat_state->var_num;
			sat_state->pending = (Lit **) malloc(
					sizeof(Lit *) * sat_state->var_num);
			sat_state->pending_num = 0;
			sat_state->pending_capacity = sat_state->var_num;
			sat_state->asserting = NULL;
		} else {
			// read each clause
			Clause * c = (Clause *) malloc(sizeof(Clause));

			c->index = clause_count + 1;
			int capacity = 5;
			c->lits = (Lit **) malloc(sizeof(Lit *) * capacity);
//			c->asserted = 0;
			c->assertion_level = 0;
			c->mark = 0;

			char * token = strtok(line, " ");
			int lit_count = 0; // count literals in this clause
			while (token) {
				int lit_index = atoi(token);
				if (lit_index == 0)
					break;
				int var_index = lit_index > 0 ? lit_index : -lit_index;
				if (lit_count >= capacity) {
					capacity *= 2;
					c->lits = (Lit **) realloc(c->lits,
							capacity * sizeof(Lit *));
				}

				// add to clause
				Lit * lit = sat_index2literal(lit_index, sat_state);
				c->lits[lit_count] = lit;

				// update lit->clauses
				add_clause_to_lit(lit, c);

				// update var->clauses
				add_clause_to_var(sat_state->vars[var_index - 1], c);

				token = strtok(NULL, " ");
				lit_count++;
			}

			if (lit_count == 0) {
				free(c->lits);
				free(c);
			} else {
				if (lit_count == 1) {
					// unit clause, no need to watch, imply immediately
					c->l1 = NULL;
					c->l2 = NULL;
					add_lit_to_implies(c->lits[0], c, sat_state);
				} else {
					// set l1 to the first literal, set l2 to the second
					c->l1 = c->lits[0];
					c->l2 = c->lits[1];
				}
				c->size = lit_count;
				sat_state->cnf[clause_count] = c;
				clause_count++;
			}
		}
	}

	if (!feof(fp)) {
		printf("%s", "Error occurs while reading cnf file. Program exit.");
		exit(1);
	}

	fclose(fp);
	if (line)
		free(line);

	return sat_state;
}

//frees the SatState
void sat_state_free(SatState* sat_state) {
	for (int i = 0; i < sat_state->var_num; i++) {
		free(sat_state->vars[i]->clauses);
		free(sat_state->vars[i]);
	}

	for (int i = 0; i < sat_state->lit_num; i++) {
		free(sat_state->lits[i]->clauses);
		free(sat_state->lits[i]);
	}

	for (int i = 0; i < sat_state->clause_num; i++) {
		free(sat_state->cnf[i]->lits);
		free(sat_state->cnf[i]);
	}

	free(sat_state->learns);
	free(sat_state->decisions);
	free(sat_state->implies);
	free(sat_state);
	return;
}

/******************************************************************************
 * Given a SatState, which should contain data related to the current setting
 * (i.e., decided literals, subsumed clauses, decision level, etc.), this function
 * should perform unit resolution at the current decision level
 *
 * It returns 1 if succeeds, 0 otherwise (after constructing an asserting
 * clause)
 *
 * There are three possible places where you should perform unit resolution:
 * (1) after deciding on a new literal (i.e., in sat_decide_literal())
 * (2) after adding an asserting clause (i.e., in sat_assert_clause(...))
 * (3) neither the above, which would imply literals appearing in unit clauses
 *
 * (3) would typically happen only once and before the other two cases
 * It may be useful to distinguish between the above three cases
 *
 * Note if the current decision level is L, then the literals implied by unit
 * resolution must have decision level L
 *
 * This implies that there must be a start level S, which will be the level
 * where the decision sequence would be empty
 *
 * We require you to choose S as 1, then literals implied by (3) would have 1 as
 * their decision level (this level will also be the assertion level of unit
 * clauses)
 *
 * Yet, the first decided literal must have 2 as its decision level
 ******************************************************************************/

// a clause is asserting only if at most one literal is at the asserting level
BOOLEAN is_asserting(Clause * clause, SatState * sat_state) {
	int count = 0;
	for (int i = 0; i < clause->size; i++) {
		Lit* lit = clause->lits[i];
		if (lit->var->decision_level == sat_state->decision_level) {
			count++;
		}
	}

	return count <= 1;
}

Lit * get_implication(Clause * clause, SatState * sat_state) {
	for (int i = sat_state->implies_num - 1; i > -1; i--) {
		Lit * lit = sat_state->implies[i];
		for (int j = 0; j < clause->size; j++) {
			Lit * lit2 = clause->lits[j];
			if (lit2->index + lit->index == 0) {
				// implication is lit, lit2 is the last falsified
				return lit;
			}
		}
	}

	return NULL;
}

int get_assertion_level(Clause * clause) {
	int max = 1;
	int second = 1;
	for (int i = 0; i < clause->size; i++) {
		Lit * lit = clause->lits[i];
		if (lit->var->decision_level > max) {
			second = max;
			max = lit->var->decision_level;
		} else if (lit->var->decision_level > second) {
			second = lit->var->decision_level;
		}
	}

	return second;
}

BOOLEAN is_resolved(Lit * lit) {
	if (lit->index > 0) {
		return lit->var->value == 0;
	} else {
		return lit->var->value == 1;
	}
}

Lit * get_non_resolved_lit(Clause * clause) {
	for (int i = 0; i < clause->size; i++) {
		Lit * lit = clause->lits[i];
		if (lit != clause->l2 && lit != clause->l1) {
			if (!is_resolved(lit)) {
				return lit;
			}
		}
	}

	return NULL;
}

void learn_clause(Clause* clause, SatState* sat_state) {
	// l2 is resolved, contradiction, learn a clause
	Clause* learn = clause;
	while (!is_asserting(learn, sat_state)) {
		// find the implication of the last falsified literal
		Lit* lit = get_implication(learn, sat_state);
		Clause* reason = lit->var->reason;
		// resolve the un-asserting clause and the reason
		Clause* resolvent = (Clause*) malloc(sizeof(Clause));
		resolvent->index = sat_state->clause_num + sat_state->learn_num + 1;
		resolvent->lits = (Lit**) malloc(
				sizeof(Lit*) * (learn->size + reason->size));
		int index = 0;
		for (int i = 0; i < learn->size + reason->size; i++) {
			Lit* lit2;
			if (i < learn->size) {
				lit2 = learn->lits[i];
			} else {
				lit2 = reason->lits[i - learn->size];
				if (lit2->redundant) {
					continue;
				}
			}
			if (lit2->index != lit->index && lit2->index + lit->index != 0) {
				resolvent->lits[index] = lit2;
				lit2->redundant = 1;
				index++;
			}
		}
		for (int i = 0; i < index; i++) {
			resolvent->lits[i]->redundant = 0;
		}
		resolvent->size = index;
		if (learn->index > sat_state->clause_num + sat_state->learn_num) {
			// free the intermediate learned clause
			free(learn->lits);
			free(learn);
		}
		learn = resolvent;
	}

	// update lit->clauses
	for(int i = 0; i < learn->size; i++){
		Lit * lit = learn->lits[i];
		add_clause_to_lit(lit, learn);
	}

	// set assertion level
	learn->assertion_level = get_assertion_level(learn);
//	learn->asserted = 0;
	sat_state->asserting = learn;
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
	Lit * pending = pop_lit_from_pending(sat_state);

	while (pending != NULL) {
		Lit * resolved = sat_index2literal(-pending->index, sat_state);

		for (int i = 0; i < resolved->clause_num; i++) {
			Clause * clause = resolved->clauses[i];
			if (resolved == clause->l1) {
				// if l1 is resolved, find a new literal to watch
				Lit * new_watch = get_non_resolved_lit(clause);
				if (new_watch == NULL) {
					// check l2
					if (!sat_instantiated_var(clause->l2->var)) {
						// l2 is free, unit clause
						add_lit_to_implies(clause->l2, clause, sat_state);
					} else if (is_resolved(clause->l2)) {
						// l2 is resolved, contradiction, learn a clause
						learn_clause(clause, sat_state);
						return 0;
					} else {
						// l2 is asserted
//						clause->asserted = 1;
					}
				} else {
					clause->l1 = new_watch;
				}
			} else if (resolved == clause->l2) {
				// if l2 is resolved, find a new literal to watch
				Lit * new_watch = get_non_resolved_lit(clause);
				if (new_watch == NULL) {
					// check l1
					if (!sat_instantiated_var(clause->l1->var)) {
						// l1 is free, unit clause
						add_lit_to_implies(clause->l1, clause, sat_state);
					} else if (is_resolved(clause->l1)) {
						// l1 is resolved, contradiction, learn a clause
						learn_clause(clause, sat_state);
						return 0;
					} else {
						// l1 is asserted
//						clause->asserted = 1;
					}
				} else {
					clause->l2 = new_watch;
				}
			}
		}
		// pop a new one
		pending = pop_lit_from_pending(sat_state);
	}

	return 1;
}

void sat_undo_unit_resolution(SatState* sat_state) {
	int dlevel = sat_state->decision_level;
	for (int i = sat_state->implies_num - 1; i > -1; i--) {
		if (sat_state->implies[i]->var->decision_level == dlevel) {
			Lit * imply = sat_state->implies[i];
//			for(int j = 0; j < imply->clause_num; j++){
//				imply->clauses[j]->asserted --;
//			}
			imply->var->value = -1;
			imply->var->reason = NULL;
			imply->var->decision_level = 0;
			imply = NULL;
			sat_state->implies_num--;
		}
	}
}

////applies unit resolution to the cnf of sat state
////returns 1 if unit resolution succeeds, 0 if it finds a contradiction
//BOOLEAN sat_unit_resolution_old(SatState* sat_state) {
//	int old = sat_state->implies_num;
//
//	do {
//		old = sat_state->implies_num;
//		for (int i = 0; i < sat_state->clause_num + sat_state->learn_num; i++) {
//			Clause * clause;
//			if (i < sat_state->clause_num) {
//				clause = sat_state->cnf[i];
//			} else {
//				clause = sat_state->learns[i - sat_state->clause_num];
//			}
//
//			if (clause->asserted == 0) {
//				BOOLEAN falsified = 1;
//				int count = 0; // count how many literals are false
//				Lit * unset_lit = NULL;
//				// recompute the result of the clause
//				for (int j = 0; j < clause->size; j++) {
//					Lit * litp = clause->lits[j];
//					if ((litp->index > 0 && litp->var->value == 1)
//							|| (litp->index < 0 && litp->var->value == 0)) {
//						// this literal is true, the clause is subsumed
//						clause->asserted ++;
//						falsified = 0;
//						break;
//					} else if ((litp->index > 0 && litp->var->value == 0)
//							|| (litp->index < 0 && litp->var->value == 1)) {
//						// this literal is false, increment the count
//						count++;
//					} else if (litp->var->value == -1) {
//						// this literal is unset
//						if (unset_lit == NULL) {
//							unset_lit = litp;
//						} else {
//							// not a unit clause, cannot resolve it
//							break;
//						}
//					}
//				}
//
//				if (!falsified) {
//					// the clause is subsumed
//					continue;
//				} else if (count == clause->size - 1) {
//					// unit clause
//					int value;
//					if (unset_lit->index > 0) {
//						value = 1;
//					} else {
//						value = 0;
//					}
//
//					unset_lit->var->value = value;
//					unset_lit->var->reason = clause;
//					unset_lit->var->decision_level = sat_state->decision_level;
//					clause->asserted ++;
//
//					if (sat_state->implies_num + 1
//							> sat_state->implies_capacity) {
//						sat_state->implies_capacity *= 2;
//						sat_state->implies = (Lit **) realloc(
//								sat_state->implies,
//								sat_state->implies_capacity * sizeof(Lit *));
//					}
//					sat_state->implies[sat_state->implies_num] = unset_lit;
//					sat_state->implies_num++;
//				} else if (count == clause->size) {
//					// there is a contradiction, learn a clause
//					Clause * learn = clause;
//					while (!is_asserting(learn, sat_state)) {
//						// find the implication of the last falsified literal
//						Lit* lit = get_implication(learn, sat_state);
//						Clause * reason = lit->var->reason;
//
//						// resolve the un-asserting clause and the reason
//						Clause * resolvent = (Clause *) malloc(sizeof(Clause));
//						resolvent->index = sat_state->clause_num
//								+ sat_state->learn_num + 1;
//						resolvent->lits = (Lit **) malloc(
//								sizeof(Lit *) * (learn->size + reason->size));
//						int index = 0;
//						for (int i = 0; i < learn->size + reason->size; i++) {
//							Lit * lit2;
//							if (i < learn->size) {
//								lit2 = learn->lits[i];
//							} else {
//								lit2 = reason->lits[i - learn->size];
//								if (lit2->redundant) {
//									continue;
//								}
//							}
//
//							if (lit2->index != lit->index
//									&& lit2->index + lit->index != 0) {
//								resolvent->lits[index] = lit2;
//								lit2->redundant = 1;
//								index++;
//							}
//						}
//
//						for (int i = 0; i < index; i++) {
//							resolvent->lits[i]->redundant = 0;
//						}
//
//						resolvent->size = index;
//						if (learn->index
//								> sat_state->clause_num
//										+ sat_state->learn_num) {
//							// free the intermediate learned clause
//							free(learn->lits);
//							free(learn);
//						}
//						learn = resolvent;
//					}
//
//					// set assertion level
//					learn->assertion_level = get_assertion_level(learn);
//					learn->asserted --;
//					sat_state->asserting = learn;
//					return 0;
//				} else {
//					// cannot resolve it, do nothing
//				}
//			}
//		}
//	} while (old < sat_state->implies_num);
//
//	return 1;
//}
//
////undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
////after sat_unit_resolution()
//void sat_undo_unit_resolution_old(SatState* sat_state) {
//	int dlevel = sat_state->decision_level;
//	for (int i = sat_state->implies_num - 1; i > -1; i--) {
//		if (sat_state->implies[i]->var->decision_level == dlevel) {
//			sat_state->implies[i]->var->value = -1;
//			sat_state->implies[i]->var->reason = NULL;
//			sat_state->implies[i]->var->decision_level = 0;
//			sat_state->implies[i] = NULL;
//			sat_state->implies_num--;
//		}
//	}
//
//	// recompute if clause is subsumed
//	for (int i = 0; i < sat_state->clause_num + +sat_state->learn_num; i++) {
//		Clause * clause;
//		if (i < sat_state->clause_num) {
//			clause = sat_state->cnf[i];
//		} else {
//			clause = sat_state->learns[i - sat_state->clause_num];
//		}
//
//		if (clause->asserted == 0) {
//			clause->asserted = 0;
//			// recompute the result of the clause
//			for (int j = 0; j < clause->size; j++) {
//				Lit * litp = clause->lits[j];
//				if ((litp->index > 0 && litp->var->value == 1)
//						|| (litp->index < 0 && litp->var->value == 0)) {
//					// this literal is true, the clause is subsumed
//					clause->asserted ++;
//					break;
//				}
//			}
//		}
//	}
//
//	sat_state->asserting = NULL;
//	return;
//}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {
	return clause->assertion_level == sat_state->decision_level;
}

/******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit) {
	return 1;
}

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var) {
	return var->mark;
}

//marks a variable (which is not marked already)
void sat_mark_var(Var* var) {
	var->mark = 1;
}

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var) {
	var->mark = 0;
}

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause) {
	return clause->mark;
}

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause) {
	clause->mark = 1;
}
//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause) {
	clause->mark = 0;
}

/******************************************************************************
 * end
 ******************************************************************************/


