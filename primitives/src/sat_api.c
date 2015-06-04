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
	Clause ** clauses = var->clauses;
	for (int i = 0; i < var->clause_num; i++) {
		Clause * clause = clauses[i];
		if (!clause->subsume)
			return 0;
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
	lit->decision_level = sat_state->decision_level + 1;
	if (sat_state->decision_capacity < sat_state->decision_level) {
		sat_state->decision_capacity += 5;
		sat_state->decisions = (Lit **) realloc(sat_state->decisions,
				sat_state->decision_capacity * sizeof(Lit *));
	}
	sat_state->decisions[sat_state->decision_level - 1] = lit;
	sat_state->decision_level++;

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
	Lit * lit = sat_state->decisions[sat_state->decision_level - 1];
	sat_state->decisions[sat_state->decision_level - 1] = NULL;
	sat_state->decision_level--;
	lit->var->value = -1;
	lit->decision_level = 0;

	sat_undo_unit_resolution(sat_state);
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
	return clause->subsume;
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
		capacity += 5;
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

void add_clause(Var * var, Clause * clause) {
	if (var->clause_num + 1 > var->clause_capacity) {
		var->clause_capacity += 10;
		var->clauses = (Clause **) realloc(var->clauses,
				var->clause_capacity * sizeof(Clause *));
	}

	var->clauses[var->clause_num] = clause;
	var->clause_num++;
}

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name) {
	FILE *fp = fopen(file_name, "r");
	const size_t len = 1024;
	char *line = (char *) malloc(len);
	SatState* sat_state = (SatState*) malloc(sizeof(SatState));
	sat_state->learns = (Clause **) malloc(sizeof(Clause *) * 10);
	sat_state->learn_num = 0;
	sat_state->learn_capacity = 10;
	sat_state->decisions = (Lit **) malloc(sizeof(Lit *) * 10);
	sat_state->decision_level = 1;
	sat_state->decision_capacity = 10;
	sat_state->implies = (Lit **) malloc(sizeof(Lit *) * 10);
	sat_state->implies_num = 0;
	sat_state->implies_capacity = 10;
	sat_state->asserting = NULL;

	if (fp == NULL) {
		printf("%s",
				"Cannot read the cnf file, please check if it exists or is broken. Program Exit.");
		exit(1);
	}

	int clause_count = 0;
	while (fgets(line, len, fp) != NULL) {
		if (startsWith("0", line) || startsWith("c", line)
				|| startsWith("%", line) || startsWith("ccc", line)
				|| startsWith("cc", line))
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
								sizeof(Clause *) * 10);
						var->clause_num = 0;
						var->clause_capacity = 10;
						var->value = -1;
						sat_state->vars[i] = var;
					}

					sat_state->lits = (Lit **) malloc(
							sizeof(Lit *) * var_num * 2);
					sat_state->lit_num = var_num * 2;
					for (int i = 0; i < var_num; i++) {
						Lit * pos = (Lit *) malloc(sizeof(Lit));
						pos->index = i + 1;
						pos->decision_level = 0;
						pos->reason = NULL;
						pos->var = sat_state->vars[i];
						Lit * neg = (Lit *) malloc(sizeof(Lit));
						neg->index = -(i + 1);
						neg->decision_level = 0;
						neg->reason = NULL;
						neg->var = sat_state->vars[i];

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
		} else {
			// read each clause
			Clause * c = (Clause *) malloc(sizeof(Clause));

			c->index = clause_count + 1;
			int capacity = 5;
			c->lits = (Lit **) malloc(sizeof(Lit *) * capacity);
			c->subsume = 0;
			c->assertion_level = 0;

			char * token = strtok(line, " ");
			int lit_count = 0; // count literals in this clause
			while (token) {
				int lit_index = atoi(token);
				if (lit_index == 0)
					break;
				int var_index = lit_index > 0 ? lit_index : -lit_index;
				if (lit_count >= capacity) {
					capacity += 5;
					c->lits = (Lit **) realloc(c->lits,
							capacity * sizeof(Lit *));
				}

				// add to clause
				Lit * lit = sat_index2literal(lit_index, sat_state);
				c->lits[lit_count] = lit;

				// update var->clauses
				add_clause(sat_state->vars[var_index - 1], c);

				token = strtok(NULL, " ");
				lit_count++;
			}

			c->size = lit_count;
			sat_state->cnf[clause_count] = c;

			clause_count++;
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
		if (lit->decision_level == sat_state->decision_level) {
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
	int max = 0;
	int second = 0;
	for (int i = 0; i < clause->size; i++) {
		Lit * lit = clause->lits[i];
		if (lit->decision_level > max) {
			max = lit->decision_level;
			second = max;
		} else if (lit->decision_level > second) {
			second = lit->decision_level;
		}
	}

	return second;
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
	int old = sat_state->implies_num;

	do {
		for (int i = 0; i < sat_state->clause_num + sat_state->learn_num; i++) {
			Clause * clause;
			if (i < sat_state->clause_num) {
				clause = sat_state->cnf[i];
			} else {
				clause = sat_state->learns[i - sat_state->clause_num];
			}

			if (!clause->subsume) {
				BOOLEAN falsified = 1;
				int count = 0; // count how many literals are false
				Lit * unset_lit = NULL;
				// recompute the result of the clause
				for (int j = 0; j < clause->size; j++) {
					Lit * litp = clause->lits[j];
					if ((litp->index > 0 && litp->var->value == 1)
							|| (litp->index < 0 && litp->var->value == 0)) {
						// this literal is true, the clause is subsumed
						clause->subsume = 1;
						falsified = 0;
						break;
					} else if ((litp->index > 0 && litp->var->value == 0)
							|| (litp->index < 0 && litp->var->value == 1)) {
						// this literal is false, increment the count
						count++;
					} else if (litp->var->value == -1) {
						// this literal is unset
						if (unset_lit == NULL) {
							unset_lit = litp;
						} else {
							// not a unit clause, cannot resolve it
							break;
						}
					}
				}

				if (!falsified) {
					// the clause is subsumed
					continue;
				} else if (count == clause->size - 1) {
					// unit clause
					int value;
					if (unset_lit->index > 0) {
						value = 1;
					} else {
						value = 0;
					}

					unset_lit->var->value = value;
					unset_lit->reason = clause;
					unset_lit->decision_level = sat_state->decision_level;
					clause->subsume = 1;

					if (sat_state->implies_num + 1
							> sat_state->implies_capacity) {
						sat_state->implies_capacity += 10;
						sat_state->implies = (Lit **) realloc(
								sat_state->implies,
								sat_state->implies_capacity * sizeof(Lit *));
					}
					sat_state->implies[sat_state->implies_num] = unset_lit;
					sat_state->implies_num++;
				} else if (count == clause->size) {
					// there is a contradiction, learn a clause
					Clause * learn = clause;
					while (!is_asserting(learn, sat_state)) {
						// find the implication of the last falsified literal
						Lit* lit = get_implication(learn, sat_state);
						Clause * reason = lit->reason;

						// resolve the un-asserting clause and the reason
						Clause * resolvent = (Clause *) malloc(sizeof(Clause));
						resolvent->index = sat_state->clause_num
								+ sat_state->learn_num;
						resolvent->lits = (Lit **) malloc(
								sizeof(Lit *) * (learn->size + reason->size));
						int index = 0;
						for (int i = 0; i < learn->size + reason->size; i++) {
							Lit * lit2;
							if (i < learn->size) {
								lit2 = learn->lits[i];
							} else {
								lit2 = learn->lits[i - learn->size];
							}

							if (lit2->index != lit->index
									|| lit2->index + lit->index != 0) {
								BOOLEAN redundant = 0;
								for (int j = 0; j < index; j++) {
									// avoid adding redundant literal
									if (lit2->index
											== resolvent->lits[j]->index) {
										redundant = 1;
									}
								}
								if (!redundant) {
									resolvent->lits[index] = lit2;
									index++;
								}
							}
						}

						resolvent->size = index;
						learn = resolvent;

						// free resolvent
						free(resolvent->lits);
						free(resolvent);
					}

					// set assertion level
					learn->assertion_level = get_assertion_level(learn);
					learn->subsume = 0;
					sat_state->asserting = learn;
					return 0;
				} else {
					// cannot resolve it, do nothing
				}
			}
		}
	} while (old < sat_state->implies_num);

	return 1;
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
	int dlevel = sat_state->decision_level;
	for (int i = sat_state->implies_num; i > -1; i--) {
		if (sat_state->implies[i]->decision_level == dlevel) {
			sat_state->implies[i]->var->value = -1;
			sat_state->implies[i]->reason = NULL;
			sat_state->implies[i]->decision_level = 0;
			sat_state->implies[i] = NULL;
			sat_state->implies_num--;
		}
	}

	// recompute if clause is subsumed
	for (int i = 0; i < sat_state->clause_num + +sat_state->learn_num; i++) {
		Clause * clause;
		if (i < sat_state->clause_num) {
			clause = sat_state->cnf[i];
		} else {
			clause = sat_state->learns[i - sat_state->clause_num];
		}

		if (clause->subsume) {
			clause->subsume = 0;
			// recompute the result of the clause
			for (int j = 0; j < clause->size; j++) {
				Lit * litp = clause->lits[j];
				if ((litp->index > 0 && litp->var->value == 1)
						|| (litp->index < 0 && litp->var->value == 0)) {
					// this literal is true, the clause is subsumed
					clause->subsume = 1;
					break;
				}
			}
		}
	}

	// free the learned clause
	if (sat_state->asserting != NULL) {
		free(sat_state->asserting->lits);
		free(sat_state->asserting);
	}
	sat_state->asserting = NULL;
	return; //dummy valued
}

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


