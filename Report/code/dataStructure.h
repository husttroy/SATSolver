typedef struct var {
	c2dSize index;
	struct literal * pos;
	struct literal * neg;
	struct clause ** clauses;
	int clause_num;
	int clause_capacity;
	int value;  // 1 --> true, 0 --> false, -1 --> unset
	BOOLEAN mark;
} Var;

typedef struct literal {
	c2dLiteral index;
	Var * var;
	int decision_level;
	struct clause * reason;
} Lit;

typedef struct clause {
	c2dSize index;
	Lit** lits;
	int size;
	BOOLEAN subsume;
	int assertion_level;
	BOOLEAN mark;
} Clause;

typedef struct sat_state_t {
	Var ** vars;
	int var_num;
	Lit ** lits;
	int lit_num;
	Clause ** cnf;
	int clause_num;
	Clause ** learns;
	int learn_num;
	int learn_capacity;
	Lit ** decisions;
	int decision_level;
	int decision_capacity;
	Lit ** implies;
	int implies_num;
	int implies_capacity;
	Clause * asserting;
} SatState;