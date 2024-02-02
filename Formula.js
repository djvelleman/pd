//Methods for formulas
"use strict";

function SymbolData(letter, inType, outType, priority) {
	this.letter = letter;
	this.inType = inType;
	this.outType = outType;
	this.priority = priority;
}

class Formula {
	constructor(kind, objType) {
		this.kind = kind;
		this.objType = objType;
		this.parens = null;
	}

	toText() {
		return this.addText("");
	}
	
	mightNeedParens() {
		return (this.kind >= conj) && (this.kind <= doubleIntr) && (this.parens == null);
	}

	addText(s) {
		this.first = s.length;
		if (this.kind == pair) {
			this.parens = "(";
		}
		if (this.parens != null) {
			s += this.parens;
		}
		s = this.addContent(s);
		if (this.parens == "(") {
			s += ")";
		} else if (this.parens == "[") {
			s += "]";
		}
		this.last = s.length - 1;
		return s;
	}

	cloneForm() {
		var clone = this.cloneFormContent();
		clone.first = this.first;
		clone.last = this.last;
		clone.parens = this.parens;
		return clone;
	}

	// Override in subclasses in which formulas are definable.
	isDefinable() {
		return false;
	}

	isHasElementDefinable() {
		return true;
	}

	define(avoidVars) {
		return this;
	}

	/* Returns result of replacing (in place) free occurrences of toReplace with replacement, which might be
either a Variable or a Formula (term).  Rename bound variables if necessary, avoiding variables in
avoidVars.  If updateAvoid, add new variable names chosen to avoidVars.  To guarantee correctness,
avoidVars must already contain all variables in original Formula and all variables in replacement.
*/
	plugIn(toReplace, replacement, avoidVars, updateAvoid) {
		this.parens = null;
		var replacementVars;
		var boundSubs = [];
		var boundReps = [];
		if ((typeof replacement) == "number") {
			replacementVars = [replacement];
		} else {
			replacementVars = [];
			replacement.addVars(replacementVars, true);
		}
		var result = this.subForVar(toReplace, replacement, replacementVars, boundSubs);
		var n = boundSubs.length;
		var v = -1;
		var i;
		for (i = 0; i < n; i++) {
			v = findNextVar(avoidVars, updateAvoid, v);
			boundReps.push(v);
		}
		result.subBoundVars(boundSubs, boundReps);
		return result;
	}

	subForTerm() {
		if (this instanceof MultiCompoundFormula) {
			return this.subForTermRange(0, this.args.length - 1);
		}
		if (formMatch(this, repInfo.toReplace, true)) {
			recordMarkedVars(repInfo.replacementVars, repInfo.boundSubs);
			var result = repInfo.replacement.cloneForm();
			result.objType = -result.objType;
			repInfo.didSub = true;
			return result;
		}
		this.subForTermInside();
		return this;
	}

	// Override in classes that have an inside
	subForTermInside() {}
	
	subBoundVars(boundSubs, boundReps) {
		if (this.objType < 0) {
			this.objType = -this.objType;
		} else {
			this.doSubBoundVars(boundSubs, boundReps);
		}
	}

	// Overide in classes where can do smarter negate.
	smartNegate(avoidVars) {
		return negate(this);
	}

	/* If assertType = 1, return formula "Ax(this(x) -> x = theVar)".
	If assertType = 2, return formula "AxAy(this(x) & this(y) -> x = y)".
	avoidVars must include all variables in formula.
	*/
	assertUnique(assertType, theVar, bound, avoidVars, updateAvoid) {
		var newVar = findNextVar(avoidVars, updateAvoid, -1);
		var var2;
		var result = new BindingFormula(all, bool, newVar, bound, null); // fill in scope later.
		var lastQfied, antecedent;
		if (assertType == 2) {
			var2 = findNextVar(avoidVars, updateAvoid, newVar);
			if (bound != null) {
				bound = bound.cloneForm();
			}
			lastQfied = new BindingFormula(all, bool, var2, bound, null); // fill in scope later.
			result.scope = lastQfied;
			var thisCopy = this.cloneForm();
			// Note no substitutions below because newVar and var2 are new.
			var newArgs = [this.plugIn(theVar, newVar, avoidVars, false), 
				thisCopy.plugIn(theVar, var2, avoidVars, false)];
			antecedent = new MultiCompoundFormula(conj, bool, newArgs);
		} else {
			antecedent = this.plugIn(theVar, newVar, avoidVars, false);
			lastQfied = result;
			var2 = theVar;
		}
		var consequent = new CompoundFormula(equals, bool, new AtomicTerm(newVar), new AtomicTerm(var2));
		lastQfied.scope = new CompoundFormula(cond, bool, antecedent, consequent);
		return result;
	}
} // End Formula
	
class AtomicTerm extends Formula {
	constructor(theVar) {
		if (theVar == -1) {
			super(empty, set);
		} else {
			super(setVar, set);
			this.theVar = theVar;
		}
	}

	hasFree(vbl) {
		return ((this.kind == setVar) && (this.theVar == vbl));
	}

	addContent(s) {
		if (this.kind == setVar) {
			return s + varToText(this.theVar);
		} else {
			return s + symbols[empty].letter;
		}
	}

	addVars(vars, freeOnly) {
		if (this.kind == setVar) {
			addElemToSet(vars, this.theVar);
		}
	}
	
	cloneFormContent() {
		if (this.kind == setVar) {
			return new AtomicTerm(this.theVar);
		} else {
			return new AtomicTerm(-1);
		}
	}

	noNegSubFormMatch(form, qVars1, qVars2) {
		if (this.kind == empty) {
			return true;
		}
		var lastQVar = qVars1.length - 1;
		var i, j;
		for (i = lastQVar; i >= 0; i--) {
			if (this.theVar == qVars1[i]) {
				for (j = lastQVar; j > i; j--) {
					if (form.theVar == qVars2[j]) {
						return false;
					}
				}
				return form.theVar == qVars2[i];
			}
		}
		for (j = lastQVar; j >= 0; j--) {
			if (form.theVar == qVars2[j]) {
				return false;
			}
		}
		return this.theVar == form.theVar;
	}

	searchSubform() {
		return true;  // Search is over;
	}
	// Don't need subCanRemoveGrouping because can't be parent of subform.

	isHasElementDefinable() {
		return (this.kind == empty);
	}

	// Only called if kind == empty
	defineHasElement(avoidVars, theElement) {
		return new CompoundFormula(notEquals, bool, theElement, theElement.cloneForm());
	}

	subForVar(toReplace, replacement, replacementVars, boundSubs) {
		var result;
		if ((this.kind == setVar) && (this.theVar == toReplace)) {
			recordMarkedVars(replacementVars, boundSubs);
			if ((typeof replacement) == "number") {
				this.theVar = replacement;
				this.objType = -this.objType;
			} else {
				result = replacement.cloneForm();
				result.objType = -result.objType;
				return result;
			}
		}
		return this;	
	}

	doSubBoundVars(boundSubs, boundReps) {
		if (this.kind == setVar) {
			var i = boundSubs.indexOf(-this.theVar - 1);
			if (i >= 0) {
				this.theVar = boundReps[i];
			}
		}
	}
} // End AtomicTerm

class CompoundFormula extends Formula {  // For unary operator, left is null
	constructor(kind, objType, left, right) {
	super(kind, objType);
	this.left = left;
	this.right = right;
	}

	hasFree(vbl) {
		return (this.right.hasFree(vbl) || ((this.kind <= pair) && this.left.hasFree(vbl)));
	}

	addContent(s) {
		if (this.kind == inverse) {
			if ((this.right.kind >= conj) && (this.right.kind <= power) && (this.right.parens == null)) {
				this.right.parens = '(';
			}
			s = this.right.addText(s);
			return s + "-";  // Use "-" as symbol for inverse in strings;
		}
		if (this.kind == power) {
			if (this.right.parens == null) { // Always use parens for power set operator
				this.right.parens = "(";
			}
			return this.right.addText(s + "\u2118"); // Correct power symbol takes two code units, so use this instead
		}
		if (this.kind <= pair) {
			if (this.left.mightNeedParens() && (symbols[this.left.kind].priority < symbols[this.kind].priority)) {
				this.left.parens = '(';
			}
			s = this.left.addText(s);
		}
		s += symbols[this.kind].letter;
		if (this.kind == doubleIntr) {
			s += symbols[this.kind].letter;
		}
		if (this.right.mightNeedParens() && (symbols[this.right.kind].priority <= symbols[this.kind].priority)) {
			this.right.parens = "(";
		}
		return this.right.addText(s);
	}	

	addVars(vars, freeOnly) {
		this.right.addVars(vars, freeOnly);
		if (this.kind <= pair) {
			this.left.addVars(vars, freeOnly);
		}
	}

	cloneFormContent() {
		var clone;
		if (this.left == null) {
			clone = new CompoundFormula(this.kind, this.objType, null, this.right.cloneForm());
		} else {
			clone = new CompoundFormula(this.kind, this.objType, this.left.cloneForm(), this.right.cloneForm());
		}
		return clone;
	}

	noNegSubFormMatch(form, qVars1, qVars2) {
		var rightMatch = subFormMatch(this.right, form.right, true, qVars1, qVars2);
		if (this.kind > pair) {
			return rightMatch;
		}
		if (rightMatch && subFormMatch(this.left, form.left, true, qVars1, qVars2)) {
			return true;
		}
		if ((this.kind == bicond) || (this.kind == symmDiff) || (this.kind == equals) || (this.kind == notEquals)) {
			return subFormMatch(this.right, form.left, true, qVars1, qVars2) &&
				subFormMatch(this.left, form.right, true, qVars1, qVars2);
		}
		return false;
	}

	searchSubform() {
		if ((mySel.start >= this.right.first) && (mySel.end <= this.right.last + 1)) {
			if (this.right.searchSubform()) {
				subformSpec.parentForm = this;
				subformSpec.subLoc = locRight;
				subformSpec.subForm = this.right;
			}
		} else if ((this.kind <= pair) && (mySel.start >= this.left.first)
				&& (mySel.end <= this.left.last + 1)) {
			if (this.left.searchSubform()) {
				subformSpec.parentForm = this;
				subformSpec.subLoc = locLeft;
				subformSpec.subForm = this.left;
			}
		} else {
			return true;
		}
		return false;
	}

	changeSubform() {
		if (subformSpec.subLoc == locLeft) {
			this.left = subformSpec.subForm;
		} else {
			this.right = subformSpec.subForm;
		}
	}
	
	subCanRemoveGrouping() {
		var subKind = subformSpec.subForm.kind;
		if (this.kind == inverse) {
			return ((subKind < conj) || (subKind > power));
		}
		if ((subKind < conj) || (subKind > doubleIntr)) {
			return true;
		}
		var parentPriority = symbols[this.kind].priority;
		var subPriority = symbols[subKind].priority;
		return ((subPriority > parentPriority) ||
			((subPriority == parentPriority) && (subformSpec.subLoc == locLeft)));
	}

	isDefinable() {
		if ((this.kind < equals) || (this.kind > notSubset)) {
			return false;
		}
		if ((this.kind == element) || (this.kind == notElement)) {
			return this.right.isHasElementDefinable();
		}
		return true;
	}

	define(avoidVars) {
		var whichKind = this.kind;
		var negated = false;
		var result;
		if ((whichKind >= notEquals) && (whichKind <= notSubset)) {
			whichKind += equals - notEquals;
			negated = true;
		}
		switch (whichKind) {
			case equals:
				var isEmpty = null;
				if (this.left.kind == empty) {
					isEmpty = this.right;
				} else if (this.right.kind == empty) {
					isEmpty = this.left;
				}
				if (isEmpty != null) {
					var newVar = findNextVar(avoidVars, true, -1);
					var varInSet =
						new CompoundFormula(element, bool, new AtomicTerm(newVar), isEmpty);
					result = new BindingFormula(exist, bool, newVar, null, varInSet);
					negated = !negated;
				} else if ((this.left.kind == pair) && (this.right.kind == pair)) {
					var newArgs = [new CompoundFormula(equals, bool, this.left.left, this.right.left),
					new CompoundFormula(equals, bool, this.left.right, this.right.right)];
					result = new MultiCompoundFormula(conj, bool, newArgs);
				} else {
					result = this.equalsSubset(avoidVars, bicond);
				}
				break;
			case element:
				result = this.right.defineHasElement(avoidVars, this.left);
				break;
			case subset:
				result = this.equalsSubset(avoidVars, cond);
		}
		if (negated) {
			return new CompoundFormula(neg, bool, null, result);
		} else {
			return result;
		}
	}

	equalsSubset(avoidVars, connective) {
		var newVar = findNextVar(avoidVars, true, -1);
		this.left = new CompoundFormula(element, bool, new AtomicTerm(newVar), this.left);
		this.right = new CompoundFormula(element, bool, new AtomicTerm(newVar), this.right);
		this.kind = connective;
		return new BindingFormula(all, bool, newVar, null, this);
	}

	defineHasElement(avoidVars, theElement) {
		var v1, v2, v3, f, newArgs;
		var leftHalf, rightHalf, pair1, pair2, pair3;
		if (this.kind == symmDiff) {
			this.kind = diff;
			leftHalf = new CompoundFormula(element, bool, theElement, this);
		//	leftHalf.parens = '(';   // Don't need this, do we?
			rightHalf = leftHalf.cloneForm();
			var otherDiff = rightHalf.right;
			f = otherDiff.left;
			otherDiff.left = otherDiff.right;
			otherDiff.right = f;
			return new MultiCompoundFormula(disj, bool, [leftHalf, rightHalf]);
		}
		this.right.parens = null;
		if (this.kind <= pair) {
			this.left.parens = null;
		}
		switch (this.kind) {
			case diff:
				newArgs = [new CompoundFormula(element, bool, theElement, this.left),
					new CompoundFormula(notElement, bool, theElement.cloneForm(), this.right)];
				return new MultiCompoundFormula(conj, bool, newArgs);
			case prod:
				if (theElement.kind == pair) {
					newArgs = [new CompoundFormula(element, bool, theElement.left, this.left),
						new CompoundFormula(element, bool, theElement.right, this.right)];
					return new MultiCompoundFormula(conj, bool, newArgs);
				} else {
					v1 = findNextVar(avoidVars, true, -1);
					v2 = findNextVar(avoidVars, true, v1);
					var orderedPair =
						new CompoundFormula(pair, set, new AtomicTerm(v1), new AtomicTerm(v2));
					return new BindingFormula(exist, bool, v1, this.left,
						new BindingFormula(exist, bool, v2, this.right,
						new CompoundFormula(equals, bool, theElement, orderedPair)));
				}
			case comp:
				v1 = findNextVar(avoidVars, true, -1);
				var finalScope;
				var pairElement = (theElement.kind == pair);
				if (pairElement) {
					pair1 = new CompoundFormula(pair, set, theElement.left, new AtomicTerm(v1));
					pair2 = new CompoundFormula(pair, set, new AtomicTerm(v1), theElement.right);
				} else {
					v2 = findNextVar(avoidVars, true, v1);
					v3 = findNextVar(avoidVars, true, v2);
					pair1 = new CompoundFormula(pair, set, new AtomicTerm(v1), new AtomicTerm(v2));
					pair2 = new CompoundFormula(pair, set, new AtomicTerm(v2), new AtomicTerm(v3));
				}
				newArgs = [new CompoundFormula(element, bool, pair1, this.right),
					new CompoundFormula(element, bool, pair2, this.left)];
				finalScope = new MultiCompoundFormula(conj, bool, newArgs);
				if (!pairElement) {
					pair3 = new CompoundFormula(pair, set, new AtomicTerm(v1), new AtomicTerm(v3));
					newArgs.push(new CompoundFormula(equals, bool, theElement, pair3));
					finalScope = new BindingFormula(exist, bool, v2, null,
						new BindingFormula(exist, bool, v3, null, finalScope));
				}
				return new BindingFormula(exist, bool, v1, null, finalScope);
			case doubleIntr:
				newArgs = [new CompoundFormula(element, bool, theElement, this.left),
					this.unaryOp(avoidVars, theElement.cloneForm(), all)];
				return new MultiCompoundFormula(conj, bool, newArgs);
			case pair:
				leftHalf = new CompoundFormula(equals, bool, theElement,
					new MultiCompoundFormula(enumSet, set, [this.left.cloneForm()]));
				rightHalf = new CompoundFormula(equals, bool, theElement.cloneForm(),
					new MultiCompoundFormula(enumSet, set, [this.left, this.right]));
				return new MultiCompoundFormula(disj, bool, [leftHalf, rightHalf]);
			case unionOne:
				return this.unaryOp(avoidVars, theElement, exist);
			case power:
				return new CompoundFormula(subset, bool, theElement, this.right);
			case inverse:
				if (theElement.kind == pair) {
					f = theElement.left;
					theElement.left = theElement.right;
					theElement.right = f;
					return new CompoundFormula(element, bool, theElement, this.right);
				}
				v1 = findNextVar(avoidVars, true, -1);
				v2 = findNextVar(avoidVars, true, v1);
				pair1 = new CompoundFormula(pair, set, new AtomicTerm(v1), new AtomicTerm(v2));
				pair2 = new CompoundFormula(pair, set, new AtomicTerm(v2), new AtomicTerm(v1));
				newArgs = [new CompoundFormula(equals, bool, theElement, pair1),
					new CompoundFormula(element, bool, pair2, this.right)];
				return new BindingFormula(exist, bool, v1, null,
					new BindingFormula(exist, bool, v2, null,
					new MultiCompoundFormula(conj, bool, newArgs)));
		}
	}
	
	unaryOp(avoidVars, theElement, qfier) {
		if (this.right.kind == rep) {
			return this.right.repStuff(avoidVars, theElement, qfier, element);
		}
		var v1 = findNextVar(avoidVars, true, -1);
		return new BindingFormula(qfier, bool, v1, this.right,
			new CompoundFormula(element, bool, theElement, new AtomicTerm(v1)));
	}

	subForVar(toReplace, replacement, replacementVars, boundSubs) {
		this.right = this.right.subForVar(toReplace, replacement, replacementVars, boundSubs);
		if (this.kind <= pair) {
			this.left = this.left.subForVar(toReplace, replacement, replacementVars, boundSubs);
		}
		return this;
	}

	subForTermInside() {
		this.right = this.right.subForTerm();
		if (this.kind <= pair) {
			this.left = this.left.subForTerm();
		}
	}	

	doSubBoundVars(boundSubs, boundReps) {
		this.right.subBoundVars(boundSubs, boundReps);
		if (this.kind <= pair) {
			this.left.subBoundVars(boundSubs, boundReps);
		}
	}

	smartNegate(avoidVars) {
		switch (this.kind) {
			case cond:
				return new MultiCompoundFormula(conj, bool, [this.left, negate(this.right)]);
			case bicond:
				if (this.left.kind == neg) {
					this.left = negate(this.left);
				} else if (this.right.kind == neg) {
					this.right = negate(this.right);
				} else if ((this.left.kind >= equals) && (this.left.kind <= notSubset)) {
					this.left = negate(this.left);
				} else {
					this.right = negate(this.right);
				}
				return this;
			default:
				return negate(this);
		}
	}
} // End CompoundFormula

class MultiCompoundFormula extends Formula {
	constructor(kind, objType, args) {
		super(kind, objType);
		this.args = args;
	}

	hasFree(vbl) {
		var e
		for (e of this.args) {
			if (e.hasFree(vbl)) {
				return true;
			}
		}
		return false;
	}

	addContent(s) {
		var separator, p, form, i, n;
		if (this.kind == enumSet) {
			s += "{";
			separator = symbols[comma].letter;
			p = symbols[comma].priority;;
		} else {
			separator = symbols[this.kind].letter;
			p = symbols[this.kind].priority;
		}
		form = this.args[0];
		if (form.mightNeedParens() && ((symbols[form.kind].priority < p) || (form.kind == this.kind))) {
			form.parens = "(";
		}
		s = form.addText(s);
		n = this.args.length;
		for (i = 1; i < n; i++) {
			s += separator;
			form = this.args[i];
			if (form.mightNeedParens() && (symbols[form.kind].priority <= p)) {
				form.parens = "(";
			}
			s = form.addText(s);
		}
		if (this.kind == enumSet) {
			s += "}";
		}
		return s;
	}

	addVars(vars, freeOnly) {
		var e
		for (e of this.args) {
			e.addVars(vars, freeOnly);
		}
	}

	cloneFormContent() {
		var newArgs = [];
		var i;
		var n = this.args.length;
		for (i = 0; i < n; i++) {
			newArgs.push(this.args[i].cloneForm());
		}
		var clone = new MultiCompoundFormula(this.kind, this.objType, newArgs);
		return clone;
	}

	noNegSubFormMatch(form, qVars1, qVars2) {
		var argForm;
		var argLength = this.args.length;
		var formArgCopy = form.args.slice(0);
		var formArgLength = formArgCopy.length;
		var i, j;
		if (argLength != formArgLength) {
			return false;
		}
		findMatch: for (i = 0; i < argLength; i++) {
			argForm = this.args[i];
			for (j = 0; j < formArgLength; j++) {
				if (subFormMatch(argForm, formArgCopy[j], true, qVars1, qVars2)) {
					formArgCopy.splice(j, 1);
					formArgLength--;
					continue findMatch;
				}
			}
			return false;
		}
		return true;
	}

	searchSubform() {
		var form1 = this.args[0];
		var form2 = this.args[this.args.length - 1];
		if ((mySel.start < form1.first) || (mySel.end > form2.last + 1)) {
			return true;
		}
		var loc = 0;
		while (mySel.start > form1.last + 1) {
			loc++;
			form1 = this.args[loc];
		}
		if (mySel.end > form1.last + 1) {
			if (this.kind == enumSet) {
				return true;
			}
			var end = loc;
			do {
				end++;
				form2 = this.args[end];
			} while (mySel.end > form2.last + 1);
			if ((loc == 0) && (end == this.args.length - 1)) {
				return true;
			}
			subformSpec.parentForm = this;
			subformSpec.subLoc = loc;
			subformSpec.subEnd = end;
			subformSpec.subForm = form1;
			return false;
		}
		if (form1.searchSubform()) {
			subformSpec.parentForm = this;
			subformSpec.subLoc = loc;
			subformSpec.subForm = form1;
		}
		return false;
	}

	changeSubform() {
		var newForm = subformSpec.subForm;
		var rangeStart = subformSpec.subLoc;
		var endStart;
		if (subformSpec.subEnd == 0) {
			endStart = rangeStart + 1;
		} else {
			endStart = subformSpec.subEnd + 1;
		}
		var argEnd;
		if (endStart == this.args.length) {
			argEnd = [];
		} else {
			argEnd = this.args.slice(endStart);
		}
		this.args.length = rangeStart;
		var argMid;
		if ((this.kind == newForm.kind) && (newForm.parens == null) && (this.kind != enumSet)) {
			argMid = newForm.args;
			subformSpec.subForm = argMid[0];
		} else {
			argMid = [newForm];
		}
		this.args = this.args.concat(argMid, argEnd);
		if (argMid.length == 1) {
			subformSpec.subEnd = 0;
		} else {
			subformSpec.subEnd = rangeStart + argMid.length - 1;
		}
	}

	subCanRemoveGrouping() {
		var subKind = subformSpec.subForm.kind;
		if ((subKind < conj) || (subKind > doubleIntr) || (subKind == this.kind)) {
			return true;
		}
		var parentPriority, subPriority;
		if (this.kind == enumSet) {
			parentPriority = symbols[comma].priority;
		} else {
			parentPriority = symbols[this.kind].priority;
		}
		subPriority = symbols[subKind].priority;
		return ((subPriority > parentPriority) ||
			((subPriority == parentPriority) && (subformSpec.subLoc == 0)));	
	}

	defineHasElement(avoidVars, theElement) {
		var i, entryConnective;
		switch (this.kind) {
			case enumSet:
				entryConnective = equals;
				this.kind = disj;
				break;
			case intr:
				entryConnective = element;
				this.kind = conj;
				break;
			case union:
				entryConnective = element;
				this.kind = disj;
		}
		var n = this.args.length;
		var nextForm = this.args[0];
		nextForm.parens = null;
		nextForm = new CompoundFormula(entryConnective, bool, theElement, nextForm);
		if (n == 1) {
			return nextForm;
		}
		this.args[0] = nextForm;
		for (i = 1; i < n; i++) {
			nextForm = this.args[i];
			nextForm.parens = null;
			this.args[i] = new CompoundFormula(entryConnective, bool, theElement.cloneForm(), nextForm);
		}
		return this;
	}	

	subForVar(toReplace, replacement, replacementVars, boundSubs) {
		var n = this.args.length;
		var i;
		for (i = 0; i < n; i++) {
			this.args[i] = this.args[i].subForVar(toReplace, replacement, replacementVars, boundSubs);
		}
		return this;
	}

	subForTermRange(start, end) {
		if (repInfo.toReplace.kind != this.kind) {
			this.finishSubForTerm(start, end);
			return this;
		}
		var toReplaceArgLength = repInfo.toReplace.args.length;
		var replaceAll = (toReplaceArgLength == this.args.length);
		if ((this.kind == enumSet) && !replaceAll) {
			this.finishSubForTerm(start, end);
			return this;
		}
		var i, j, argForm, result;
		var toReplaceArgCopy = repInfo.toReplace.args.slice(0);
		var shift = toReplaceArgLength - 1;
		var toMatch = toReplaceArgLength;
		findMatch: for (i = start; i <= end + 1 - toMatch; i++) {
			argForm = this.args[i];
			for (j = 0; j < toReplaceArgLength; j++) {
				if (formMatch(argForm, toReplaceArgCopy[j], true)) {
					var x = toReplaceArgCopy[j];
					toReplaceArgCopy.splice(j, 1);
					toReplaceArgCopy.push(x);
					if (j < toMatch) {
						toMatch--;
						if (toMatch == 0) {
							recordMarkedVars(repInfo.replacementVars, repInfo.boundSubs);
							result = repInfo.replacement.cloneForm();
							result.objType = -result.objType;
							repInfo.didSub = true;
							if (replaceAll) {
								return result;
							}
							i -= shift;
							end -= shift;
							this.args.splice(i, toReplaceArgLength, result);
							toMatch = toReplaceArgLength;
						}
					} else {
						toMatch = j;
					}
					continue findMatch
				}
			}
			this.args[i] = argForm.subForTerm();
			toMatch = toReplaceArgLength;
		}
		this.finishSubForTerm(i, end);
		return this;
	}

	finishSubForTerm(start, end) {
		var i;
		for (i = start; i <= end; i++) {
			this.args[i] = this.args[i].subForTerm();
		}
	}	

	doSubBoundVars(boundSubs, boundReps) {
		var a;
		for (a of this.args) {
			a.subBoundVars(boundSubs, boundReps);
		}
	}

	smartNegate(avoidVars) {
		// Only called for boolean, so kind is either conj or disj
		this.kind = conj + disj - this.kind;
		var n = this.args.length;
		var i;
		for (i = 0; i < n; i++) {
			this.args[i] = negate(this.args[i]);
		}
		return this;
	}
} // End MultiCompoundFormula

class BindingFormula extends Formula {
	constructor(kind, objType, bdVar, from, scope) {
		super(kind, objType);
		this.bdVar = bdVar;
		this.from = from;
		this.scope = scope;
	}

	hasFree(vbl) {
		return ((this.bdVar != vbl) &&
		(this.scope.hasFree(vbl) || ((this.from != null) && this.from.hasFree(vbl))));
	}

	addContent(s) {
		if (this.kind == sep) {
			return this.scope.addText(this.from.addText(s + "{" + varToText(this.bdVar)
				+ symbols[element].letter) + "|") + "}";
		}
		if (this.kind == rep) {
			return this.from.addText(this.scope.addText(s + "{")
				+ "|" + varToText(this.bdVar) + symbols[element].letter) + "}";
		}
		//quantifiers
		if (this.kind == unique) {
			s += symbols[exist].letter;
		}
		s += symbols[this.kind].letter + varToText(this.bdVar);
		if (this.from != null) {
			s += symbols[element].letter;
			if (this.from.mightNeedParens()) {
					this.from.parens = "(";
			}
			s = this.from.addText(s);
		}
		if (this.scope.mightNeedParens()) {
			this.scope.parens = "(";
		}
		return this.scope.addText(s);
	}

	addVars(vars, freeOnly) {
		var unseen = !vars.includes(this.bdVar);
		if (unseen && !freeOnly) {
			vars.push(this.bdVar);
			unseen = false;
		}
		if (this.from != null) {
			this.from.addVars(vars, freeOnly);
		}
		this.scope.addVars(vars, freeOnly);
		if (unseen) {
			var i = vars.indexOf(this.bdVar);
			if (i >= 0) {
				vars.splice(i, 1);
			}
		}
	}

	cloneFormContent() {
		var clone;
		if (this.from == null) {
			clone = new BindingFormula(this.kind, this.objType, this.bdVar, null, this.scope.cloneForm());
		} else {
			clone = new BindingFormula(this.kind, this.objType, this.bdVar, this.from.cloneForm(), this.scope.cloneForm());
		}
		return clone;
	}

	noNegSubFormMatch(form, qVars1, qVars2) {
		var fFrom = form.from;
		if (this.from == null) {
			if (fFrom != null) {
				return false;
			}
		} else {
			if ((fFrom == null) || !subFormMatch(this.from, fFrom, true, qVars1, qVars2)) {
				return false;
			}
		}
		qVars1.push(this.bdVar);
		qVars2.push(form.bdVar);
		var result = subFormMatch(this.scope, form.scope, true, qVars1, qVars2);
		qVars1.pop();
		qVars2.pop();
		return result;
	}

	searchSubform() {
		if ((mySel.start >= this.scope.first) && (mySel.end <= this.scope.last + 1)) {
			if (this.scope.searchSubform()) {
				subformSpec.parentForm = this;
				subformSpec.subLoc = locScope;
				subformSpec.subForm = this.scope;
			}
		} else if ((this.from != null) && (mySel.start >= this.from.first) && (mySel.end <= this.from.last + 1)) {
			if (this.from.searchSubform()) {
				subformSpec.parentForm = this;
				subformSpec.subLoc = locFrom;
				subformSpec.subForm = this.from;
			}
		} else {
			return true;
		}
		addElemToSet(subformSpec.boundVars, this.bdVar);
		return false;
	}

	changeSubform() {
		if (subformSpec.subLoc == locScope) {
			this.scope = subformSpec.subForm;
		} else {
			this.from = subformSpec.subForm;
		}
	}	

	subCanRemoveGrouping() {
		var subKind = subformSpec.subForm.kind;
		return ((this.kind > unique) || (subKind < conj) || (subKind > doubleIntr));
	}

	isDefinable() {
		if (this.kind == unique) {
			return true;
		}
		if ((this.kind == all) || (this.kind == exist)) {
			return (this.from != null);
		}
		return false;
	}

	define(avoidVars) {
		var newArgs;
		if (this.kind == unique) {
			var scopeCopy = this.scope.cloneForm();
			var fromCopy;
			if (this.from == null) {
				fromCopy = null;
			} else {
				fromCopy = this.from.cloneForm();
			}
			this.scope.parens = null;
			newArgs = [this.scope, scopeCopy.assertUnique(1, this.bdVar, fromCopy, avoidVars, true)];
			this.scope = new MultiCompoundFormula(conj, bool, newArgs);
			this.kind = exist;
		} else { // Define bounded quantifier
			var fromForm = new CompoundFormula(element, bool, new AtomicTerm(this.bdVar), this.from);
			this.from = null;
			this.scope.parens = null;
			if (this.kind == all) {
				this.scope = new CompoundFormula(cond, bool, fromForm, this.scope);
			} else {
				newArgs = [fromForm, this.scope];
				this.scope = new MultiCompoundFormula(conj, bool, newArgs);
			}
		}
		return this;		
	}

	defineHasElement(avoidVars, theElement) {
		if (this.kind == sep) {
			var newArgs = [new CompoundFormula(element, bool, theElement, this.from),
				this.scope.plugIn(this.bdVar, theElement, avoidVars, true)];
				// Note plugIn will clone theElement when it uses it, so don't need to clone here:
			return new MultiCompoundFormula(conj, bool, newArgs);
		} else { // rep
			return this.repStuff(avoidVars, theElement, exist, equals);
		}
	}

	repStuff(avoidVars, theElement, qfier, connective) {
		var repScope = this.scope;
		var newVar = this.bdVar;
		if (theElement.hasFree(newVar)) {
			newVar = findNextVar(avoidVars, true, -1);
			repScope.plugIn(this.bdVar, newVar, avoidVars, true);
		}
		return new BindingFormula(qfier, bool, newVar, this.from,
			new CompoundFormula(connective, bool, theElement, repScope));
	
	}

	subForVar(toReplace, replacement, replacementVars, boundSubs) {
		if (this.bdVar != toReplace) {
			var unmarkedLoc = replacementVars.indexOf(this.bdVar);
			if (unmarkedLoc >= 0) {
				replacementVars[unmarkedLoc] = -this.bdVar - 1; // Indicate bdvar is bound.
			}
			if (this.from != null) {
				this.from = this.from.subForVar(toReplace, replacement, replacementVars, boundSubs);
			}
			this.scope = this.scope.subForVar(toReplace, replacement, replacementVars, boundSubs);
			if (unmarkedLoc >= 0) {
				var markedLoc = replacementVars.indexOf(-this.bdVar - 1);
				if (markedLoc >= 0) {
					replacementVars[markedLoc] = this.bdVar;
				}
			}
		}
		return this;	
	}

	subForTermInside() {
		if (!repInfo.toReplaceVars.includes(this.bdVar)) {
			var replacementVars = repInfo.replacementVars;
			var unmarkedLoc = replacementVars.indexOf(this.bdVar);
			if (unmarkedLoc >= 0) {
				replacementVars[unmarkedLoc] = -this.bdVar - 1;
			}
			if (this.from != null) {
				this.from = this.from.subForTerm();
			}
			this.scope = this.scope.subForTerm();
			if (unmarkedLoc >= 0) {
				var markedLoc = replacementVars.indexOf(-this.bdVar - 1);
				if (markedLoc >= 0) {
					replacementVars[markedLoc] = this.bdVar;
				}
			}
		}
	}
	
	doSubBoundVars(boundSubs, boundReps) {
		if (this.from != null) {
			this.from.subBoundVars(boundSubs, boundReps);
		}
		var activeLoc;
		var inactiveLoc = boundSubs.indexOf(this.bdVar);
		if (inactiveLoc >= 0) {
			boundSubs[inactiveLoc] = -this.bdVar - 1;
			activeLoc = inactiveLoc;
		} else {
			activeLoc = boundSubs.indexOf(-this.bdVar - 1);
		}
		this.scope.subBoundVars(boundSubs, boundReps);
		if (activeLoc >= 0) {
			this.bdVar = boundReps[activeLoc];
			if (inactiveLoc >= 0) {
				boundSubs[inactiveLoc] = this.bdVar;
			}
		}
	}

	smartNegate(avoidVars) {
		if (this.kind == unique) {
			var v1 = findNextVar(avoidVars, true, -1);
			var v2 = findNextVar(avoidVars, true, v1);
			var f1 = this.cloneForm();
			f1.kind = exist;
			var f2 = f1.cloneForm();
			f1.bdVar = v1;
			f2.bdVar = v2;
			var f3 = new AtomicTerm(v1);
			var f4 = new AtomicTerm(v2);
			var newArgs = [f1.scope.plugIn(this.bdVar, v1, avoidVars, true),
					f2.scope.plugIn(this.bdVar, v2, avoidVars, true),
					new CompoundFormula(notEquals, bool, f3, f4)];
			f1.scope = f2;
			f2.scope = new MultiCompoundFormula(conj, bool, newArgs);
			this.kind = all;
			this.scope = negate(this.scope);
			f3 = new MultiCompoundFormula(disj, bool, [this, f1]);
			f3.parens = this.parens;
			return f3;
		} else {
			this.kind = all + exist - this.kind;
			this.scope = negate(this.scope);
			return this;
		}
	}	
} // End BindingFormula

function recordMarkedVars(replacementVars, boundSubs) {
	var n = replacementVars.length;
	var i = 0;
	while (i < n) {
		if (replacementVars[i] < 0) {
			boundSubs.push(-replacementVars[i] - 1);
			replacementVars.splice(i, 1);
			n--;
		} else {
			i++;
		}
	}
}

function cloneFormWithText(fwt) {
	return {theForm: fwt.theForm.cloneForm(), theText: fwt.theText};
}

function makeStmnt(form) {
	return [{theForm: form, theText: form.toText()}];
}

function cloneStmnt(stmnt) {
	var clone = [];
	var n = stmnt.length;
	var i;
	for (i = 0; i < n; i++) {
		clone.push(cloneFormWithText(stmnt[i]));
	}
	return clone;
}

/* Determine if this and form match (if same) or one is negative of other (if not), with
free variables in this from qVars1 matching free variables in form from qVars2.
*/
function subFormMatch(form1, form2, same, qVars1, qVars2) {
	var extraNeg = null;
	while ((form1.kind == neg) && (form2.kind == neg)) {
		form1 = form1.right;
		form2 = form2.right;
	}
	if (form1.kind == neg) {
		extraNeg = form1;
		form1 = form1.right;
	} else if (form2.kind == neg) {
		extraNeg = form2;
		form2 = form2.right;
	}
	if (same == (extraNeg == null)) {
		if (form1.kind != form2.kind) {
			return false;
		}
		return form1.noNegSubFormMatch(form2, qVars1, qVars2);
	}
	var posForm;
	if ((form1.kind >= equals) && (form1.kind <= subset)) {
		if (form2.kind != form1.kind + notEquals - equals) {
			return false;
		}
		posForm = form1;
	} else if ((form2.kind >= equals) && (form2.kind <= subset)) {
		if (form1.kind != form2.kind + notEquals - equals) {
			return false;
		}
		posForm = form2;
	} else {
		return false;
	}
	if (same && (extraNeg != posForm)) {
		return false;
	}
	if (subFormMatch(form1.left, form2.left,	true, qVars1, qVars2) &&
			subFormMatch(form1.right, form2.right, true, qVars1, qVars2)) {
		return true;
	}
	return ((posForm.kind == equals) &&
		subFormMatch(form1.left, form2.right, true, qVars1, qVars2) &&
		subFormMatch(form1.right, form2.left, true, qVars1, qVars2));
}

/* Determine if form1 and form2 match (if same) or one is negative of other (if not).
*/
function formMatch(form1, form2, same) {
	var qVars1 = [];
	var qVars2 = [];
	return subFormMatch(form1, form2, same, qVars1, qVars2);
}

function negate(form) {
	if ((form.kind >= equals) && (form.kind <= notSubset)) {
		if (form.kind <= subset) {
			form.kind += notEquals - equals;
		} else {
			form.kind += equals - notEquals;
		}
		form.parens = null;
		return form;
	}
	if (form.kind == neg) {
		form.right.parens = null;
		return form.right;
	}
	return new CompoundFormula(neg, bool, null, form);
}

function negateStmnt(stmnt) {
	var n = stmnt.length;
	var result = [];
	var i;
	for (i = 0; i < n; i++) {
		var neg = negate(stmnt[i].theForm.cloneForm());
		result.push({theForm: neg, theText: neg.toText()});
	}
	return result;
}

function textToElem(str, tag, includeWordBreaks) {
	var e = document.createElement(tag);
	e.className = "formula";
	e.innerHTML = textToHTML(str, includeWordBreaks);
	return e;
}

function textToElemHTML(str, tag, includeWordBreaks) {
	return "<" + tag + " class='formula'>" + textToHTML(str, includeWordBreaks) + "</" + tag + ">";
}

function textToHTML(str, includeWordBreaks) {
	var i, c;
	var l = str.length;
	var html = "";
	for (i = 0; i < l; i++) {
		c = str.charAt(i);
		if (isLetter(c)) {
			html += "<i>" + c + "</i>";
		} else if (isDigit(c)) {
			html += "<sub>" + c + "</sub>";
		} else if (c == "-") {
			html += "<sup>" + symbols[inverse].letter + "</sup>";
		} else {
			if (c == "\u2118") {
				c = symbols[power].letter;
			}
			html += "<span>" + c;
			if (includeWordBreaks && breakAfter.includes(c)) {
				html += "<wbr>";
			}
			html += "</span>";
		}
	}
	return html;
}

function isLetter(x) {
	return (((x >= "a") && (x <= "z")) || ((x >= "A") && (x <= "Z")));
}

function isDigit(x) {
	return ((x >= "0") && (x <= "9"));
}

function varFromText(theLetter, subscript) { // subscript -1 means no subscript
	var letCode = theLetter.charCodeAt(0);
	if (letCode >= 97) {
		letCode = letCode - 97;  //a-z become 0-25
	} else {
		letCode = letCode - 39;  //A-Z become 26-51
	}
	return 52 * (subscript + 1) + letCode;
}

function varToTextObj(theVar) {
	var letCode = theVar % 52;
	var theLetter
	if (letCode < 26) {
		theLetter = String.fromCharCode(97 + letCode);  //0-25 become a-z
	} else {
		theLetter = String.fromCharCode(39 + letCode);  //26-51 become A-Z
	}
	return {letter: theLetter, subscript: (theVar - letCode)/52 - 1};  //Subscript -1 means no subscript
}

function varToText(theVar) {
	var vto = varToTextObj(theVar);
	var s = vto.letter;
	if (vto.subscript >= 0) {
		s += vto.subscript.toString();
	}
	return s;
}

// Return first var > start that is not in avoidVars.  If updateAvoid, add result to avoidVars.
// Pass -1 to start search at beginning.
function findNextVar(avoidVars, updateAvoid, start) {
	do {
		start++;
	} while (avoidVars.includes(start));
	if (updateAvoid) {
		avoidVars.push(start);
	}
	return start;
}

function parseVar(txt) {
	var c = txt.childNodes;
	var n = c.length;
	if (n == 0) {
		return null;
	}
	var ltr = c[0].firstChild.textContent;
	if (!isLetter(ltr)) {
		return null;
	}
	if (n == 1) {
		return varFromText(ltr, -1);
	}
	if (n > 4) {
		return null;
	}
	var s = "";
	var i, d;
	for (i = 1; i < n; i++) {
		d = c[i].firstChild.textContent;
		if (!isDigit(d)) {
			return null;
		}
		s += d;
	}
	return varFromText(ltr, parseInt(s));
}

function parse(txt, theType, reportErrors = true) {
//txt is an element (DIV or SPAN) containing text to be parsed.
//theType is the expected type.

// Bounding values for operators
	const unbounded = 0;
	const needBound = 1;
	const foundBound = 2;
	
	var operators = [new GroupingOperator("(")];
	var operands = [];
	var position = 0;
	var nextChar = txt.childNodes[0].firstChild.textContent;
	var lastPos = txt.childNodes.length - 1;
	var state = 1;
	var form, form2, op;
	var match, i, v, k, topBdg, entries, num;

	function Operator(opNum, bounding = unbounded) { // unary or binary op
		this.opNum = opNum;
		this.bounding = bounding;
	}

	function GroupingOperator(kind) { // (, [
		this.opNum = grouping;
		this.bounding = unbounded;
		this.kind = kind;
	}

	function BindingOperator(opNum, bounding, bdVar) { // {, all, exist, unique
		this.opNum = opNum;
		this.bounding = bounding;
		this.bdVar = bdVar;
	}

	function afterError() {
		txt.focus();
		updateSelection(txt, position, position);
	}

	function parseError(msg) {
		if (reportErrors) {
			showMessage(msg, afterError);
		}
	}

	function advance() {
		position++;
		if (position <= lastPos) {
			nextChar = txt.childNodes[position].firstChild.textContent;
		} else {
			nextChar = null;
		}
	}

	function getVar() { // When called, nextChar is a letter
		var l = nextChar;
		advance();
		var s = "";
		while ((nextChar != null) && isDigit(nextChar)) {
			if (s.length >= 3) {
				parseError("Subscript too large.");
				return -1;
			}
			s += nextChar;
			advance();
		}
		if (s.length > 0) {
			return varFromText(l,parseInt(s));
		} else {
			return varFromText(l,-1);
		}
	}

	function varInSet(f) {
		if ((f.kind != element) || (f.left.kind != setVar)) {
			parseError("Incorrect set-builder notation.");
			return -1;
		}
		var v = f.left.theVar;
		if (f.right.hasFree(v)) {
			parseError("Incorrect set-builder notation.");
			return -1;
		}
		return v;
	}

	function popOp() {
		var poppedOp = operators.pop();
		var poppedForm = operands.pop();
		var poppedForm2, nextOp;
		var num = poppedOp.opNum;
		if (poppedForm.objType != symbols[num].inType) {
			parseError("Statement where term expected, or term where statement expected.");
			return null;
		}
		nextOp = operators[operators.length-1];
		if ((num >= comma) && (num <= union)) { // comma, conj, disj, intr, union
			poppedForm2 = operands[operands.length - 1];
			if ((poppedForm2.kind == num) && (poppedForm2.parens == null)) {
				poppedForm2.args.push(poppedForm);
				return nextOp;
			}
			operands[operands.length - 1] = 
				new MultiCompoundFormula(num, symbols[num].outType, [poppedForm2, poppedForm]);
			return nextOp;
		}
		if ((num >= cond) && (num <= power)) {
			if (num <= doubleIntr) { // cond, bicond, symmDiff, diff, prod, comp,
				// equals, element, subset, notEquals, notElement, notSubset, doubleIntr
				poppedForm2 = operands.pop();
			} else { // pair, neg, unionOne, power
				poppedForm2 = null;
			}
			operands.push(new CompoundFormula(num, symbols[num].outType, poppedForm2, poppedForm));
			return nextOp;	
		}
		if ((num >= all) && (num <= unique)) { // all, exist, unique
			if (poppedOp.bounding == foundBound) {
				poppedForm2 = operands.pop();
			} else {
				poppedForm2 = null;
			}
			operands.push(new BindingFormula(num, bool, poppedOp.bdVar, poppedForm2, poppedForm));
			return nextOp;
		}
	}

	processChar: while (true) {
		if (state == 1) {
		//Looking for an object
			if ((nextChar == '(') || (nextChar == '[')) {
				operators.push(new GroupingOperator(nextChar));
				advance();
				continue processChar;
			}
			if (nextChar == '{') {
				advance();
				if (nextChar != '}') {
					operators.push(new BindingOperator(brace, unbounded, null));
					continue processChar;
				}
				nextChar = symbols[empty].letter;  //Fudge to get {} to be null set.
			}
			if (nextChar == symbols[empty].letter) {
				advance();
				operands.push(new AtomicTerm(-1));
				state = 2;
				continue processChar;
			}
			if (isLetter(nextChar)) {
				v = getVar();
				if (v == -1) {
					return null;
				}
				operands.push(new AtomicTerm(v));
				state = 2;
				continue processChar;
			}
			topBdg = operators[operators.length - 1].bounding;
			for (i = neg; i <= power; i++) { // neg, unionOne, power
				if (nextChar == symbols[i].letter) {
					advance();
					operators.push(new Operator(i, (topBdg == needBound)?needBound:unbounded));
					continue processChar;
				}
			}
			if (topBdg != needBound) {
				for (i = all; i <= exist; i++) { // all, exist
					if (nextChar == symbols[i].letter) {
						advance();
						if ((i == exist) && (nextChar == symbols[unique].letter)) {
							i = unique;
							advance();
						}
						if (!isLetter(nextChar)) {
							parseError("Quantifier symbol must be followed by variable.");
							return null;
						}
						v = getVar();
						if (v == -1) {
							return null;
						}
						if (nextChar == symbols[element].letter) {
							topBdg = needBound;
							advance();
						} else {
							topBdg = unbounded;
						}
						operators.push(new BindingOperator(i, topBdg, v));
						continue processChar;
					}
				}
			}
			if (nextChar == null) {
				parseError("Incomplete expression.");
			} else {
				parseError("Illegal expression.");
			}
			return null;
		} else {
		//Looking for a binary operator
			if (nextChar == symbols[inverse].letter) { // inverse
				advance();
				form = operands.pop();
				if (form.objType != set) {
					parseError("Statement where term expected, or term where statement expected.");
					return null;
				}
				operands.push(new CompoundFormula(inverse, set, null, form));
				continue processChar;
			}
			op = operators[operators.length - 1];
			if (op.bounding == needBound) {
				while (op.opNum < all) { // op is neg, unionOne, power
					op = popOp();
					if (op == null) {
						return null;
					}
				}
				// op is now all, exist, unique
				form = operands[operands.length - 1];
				if (form.objType != set) {
					parseError("Statement where term expected, or term where statement expected.");
					return null;
				}
				if (form.hasFree(op.bdVar)) {
					parseError("Illegal bounded quantifier.");
					return null;
				}
				op.bounding = foundBound;
				state = 1;
				continue processChar;
			}
			if ((nextChar == ')') || (nextChar == ']')) {
				op = operators[operators.length - 1];
				while (op.opNum < sep) {
					op = popOp();
					if (op == null) {
						return null;
					}
				}
				operators.pop();
				if ((operators.length == 0) || (op.opNum != grouping)) {
					parseError("Unmatched parenthesis, bracket, or brace.");
					return null;
				}
				k = op.kind;
				if (((k == '(') && (nextChar == ']')) ||
					((k == '[') && (nextChar == ')'))) {
					parseError("Unmatched parenthesis, bracket, or brace.");
					return null;
				}
				form = operands[operands.length - 1];
				advance();
				if (form.objType == list) {
					entries = form.args;
					if ((k != '(') || (entries.length != 2)) {
						parseError("Illegal use of parentheses or brackets.");
						return null;
					}
					form = new CompoundFormula(pair, set, entries[0], entries[1]);
					operands[operands.length - 1] = form;
				}
				form.parens = k;
				continue processChar;
			}
			if (nextChar == '}') {
				advance();
				op = operators[operators.length - 1];
				while (op.opNum < sep) {
					op = popOp();
					if (op == null) {
						return null;
					}
				}
				operators.pop();
				switch (op.opNum) {
					case grouping: // (, [
						parseError("Unmatched parenthesis, bracket, or brace.");
						return null;
					case brace:
						form = operands[operands.length - 1];
						switch (form.objType) {
							case set:
								operands[operands.length - 1] = new MultiCompoundFormula(enumSet, set, [form]);
								continue processChar;
							case bool:
								parseError("Incorrect set-builder notation.");
								return null;
							case list:
								form.kind = enumSet;
								form.objType = set;
								continue processChar;
						}
					case sep:
						form = operands.pop();
						if (form.objType != bool) {
							parseError("Incorrect set-builder notation.");
							return null;
						}
						form2 = operands.pop();
						operands.push(new BindingFormula(sep, set, op.bdVar, form2, form));
						continue processChar;
					case rep:
						form = operands.pop();
						form2 = operands.pop();
						v = varInSet(form);
						if (v == -1) {
							return null;
						}
						operands.push(new BindingFormula(rep, set, v, form.right, form2));
						continue processChar;
				}
			}
			if (nextChar == '|') {
				advance();
				state = 1;
				op = operators[operators.length - 1];
				while (op.opNum < sep) {
					op = popOp();
					if (op == null) {
						return null;
					}
				}
				if (op.opNum != brace) {
					parseError("Illegal use of \"|\".");
					return null;
				}
				form = operands[operands.length - 1];
				if (form.objType == set) {
					op.opNum = rep;
				} else {
					op.opNum = sep;
					op.bdVar = varInSet(form);
					if (op.bdVar == -1) {
						return null;
					}
					operands[operands.length - 1] = form.right;
				}
				continue processChar;
			}
			for (i = comma; i <= notSubset; i++) { // comma, conj, disj, intr, union, cond, bicond, 
				// symmDiff, diff, prod, comp, equal, element, subset, notEquals, notElement, notSubset
				if (nextChar == symbols[i].letter) {
					advance();
					state = 1;
					if ((i == intr) && (nextChar == symbols[intr].letter)) {
						advance();
						i = doubleIntr;
					}
					op = operators[operators.length - 1];
					popping: do {
						num = op.opNum;
						form = operands[operands.length - 1];
						match = ((symbols[i].inType == form.objType) ||
							((i == comma) && (form.objType == list)));
						if (num >= sep) {
							break popping;
						}
						if (symbols[num].inType != form.objType) {
							break popping;
						}
						if ((num <= doubleIntr) && (match && (symbols[num].priority < symbols[i].priority))) {
							break popping;
						}
						op = popOp();
						if (op == null) {
							return null;
						}
					} while (true);
					if (!match) {
						parseError("Statement where term expected, or term where statement expected.");
						return null;
					}
					operators.push(new Operator(i));
					continue processChar;
				}
			}
			if (nextChar == null) {
				//End of input string
				op = operators[operators.length - 1];
				while (op.opNum < sep) {
					op = popOp();
					if (op == null) {
						return null;
					}
				}
				operators.pop();
				if (operators.length > 0) {
					parseError("Unmatched parenthesis, bracket, or brace.");
					return null;
				}
				form = operands.pop();
				if (form.objType != theType) {
					parseError("Statement where term expected, or term where statement expected.");
					return null;
				}
				return form;
			}
			parseError("Illegal expression.");
			return null;
		}
	}
}
