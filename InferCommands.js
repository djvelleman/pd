// Infer menu commands
"use strict";

function doMPMT(mp) {
	if (mp) {
		helpURL = "help/MP.html";
		commandName = "Modus Ponens";
	} else {
		helpURL = "help/MT.html";
		commandName = "Modus Tollens";
	}
  if (selection.length != 2) {
    useError();
    return;
  }
	var selectedPane1 = selection[0];
  var pane1Data = getData(selectedPane1.parentNode);
  if (pane1Data.kind == defineGoal) {
    useError();
    return;
  }
  var selectedPane2 = selection[1];
  var pane2Data = getData(selectedPane2.parentNode);
  var forwards = (pane1Data.kind == given);
  var stmnt1 = pane1Data.theStmnt;
  if (stmnt1 == null) {
    useError();
    return;
  }
  var stmnt2 = pane2Data.theStmnt;
  var form1 = stmnt1[getData(selectedPane1).variant].theForm;
  var form2 = stmnt2[getData(selectedPane2).variant].theForm;
  var swapped = false;
  var newStmnt, newForm;
	do {
		if (form2.kind == cond) {
			if (mp == forwards) {
				if (formMatch(form1, form2.left, forwards)) {
					break;
				}
			} else {
				if (formMatch(form1, form2.right, !forwards)) {
					break;
				}
			}
		}
		if (swapped || !forwards) {
			useError();
			return;
		}
		newStmnt = stmnt1;
		stmnt1 = stmnt2;
		stmnt2 = newStmnt;
		newForm = form1;
		form1 = form2;
		form2 = newForm;
		swapped = true;
	} while (true);
	if (mp == forwards) {
		newForm = form2.right;
	} else {
		newForm = form2.left;
	}
	newForm = newForm.cloneForm();
  newForm.parens = null;
  if (!mp) {
		newForm = negate(newForm);
	}
	newStmnt = makeStmnt(newForm);
  if (forwards) {
    forwardStep(selectedStep, null, [stmnt1, stmnt2], null, [newStmnt], null, false);
  } else {
    backwardStep(selectedStep, null, [newStmnt], [newStmnt, stmnt2], null)
  }
}

function doSplitUp() {
	helpURL = "help/SplitUp.html";
	commandName = "Split Up";
	if (!gapSelected(false)) {
		useError();
		return;
	}
	var selGivenFWT = getGivenVariant(anyKind);
	if (selGivenFWT == null) {
		useError();
		return;
	}
	var selForm = selGivenFWT.theForm;
	var infStmnts;
	switch (selForm.kind) {
		case conj:
			var args = selForm.args;
			var numArg = args.length;
			infStmnts = [];
			var i;
			for (i = 0; i < numArg; i++) {
				var nextArg = args[i].cloneForm();
				nextArg.parens = null;
				infStmnts.push(makeStmnt(nextArg));
			}
			break;
		case bicond:
			var left = selForm.left;
			var right = selForm.right;
			var ltor = new CompoundFormula(cond, bool, left.cloneForm(), right.cloneForm());
			var rtol = new CompoundFormula(cond, bool, right.cloneForm(), left.cloneForm());
			infStmnts = [makeStmnt(ltor), makeStmnt(rtol)];
			break;
		default:
			useError();
			return;
	}
	var givenStmnt = getData(selection[0].parentNode).theStmnt;
	forwardStep(selectedStep, null, [givenStmnt], null, infStmnts, null, false);
}

function doAddition() {
	var givenStmnt, goalStmnt, goalForm, goalArgs;
	var givenFWT, entryField, okButton, defined;

	function afterError() {
		entryField.focus();
	}

	function finishAddition() {
		var entryForm = parse(entryField, bool);
		if (entryForm == null) {
			return;
		}
		if (!checkDefined(defined, entryForm, afterError)) {
			return;
		}
		hideDialog();
		goalArgs = [];
		addToList(givenFWT.theForm.cloneForm(), goalArgs, disj);
		addToList(entryForm, goalArgs, disj);
		forwardStep(selectedStep, null, [givenStmnt], null,
			[makeStmnt(new MultiCompoundFormula(disj, bool, goalArgs))], null, false);
	}

	function setOKButton() {
		okButton.disabled = (entryField.childNodes.length == 0);
	}

	helpURL = "help/Addition.html";
	commandName = "Addition";
	if (!gapSelected(false)) {
		useError();
		return;
	}
	var numSelected = selection.length;
	if (numSelected == 2) {
		var goalData = getData(selection[0].parentNode);
		if (goalData.kind != goal) {
			useError();
			return;
		}
		goalStmnt = goalData.theStmnt;
		if (goalStmnt == null) {
			useError();
			return;
		}
		goalForm = goalStmnt[getData(selection[0]).variant].theForm;
		if (goalForm.kind != disj) {
			useError();
			return;
		}
		finishByAddition(goalForm);
		return;
	}
	if (numSelected != 1) {
		useError();
		return;
	}
	var givenData = getData(selection[0].parentNode);
	if (givenData.kind != given) {
		useError();
		return;
	}
	givenStmnt = givenData.theStmnt;
	defined = getData(selectedStep).defined;
	givenFWT = givenStmnt[getData(selection[0]).variant];
	var theDialog = makeDialog(42);
	theDialog.appendChild(mathPal);
	var formPane = textToElem(givenFWT.theText, "div", true);
	formPane.style.marginTop = "0.66em";
	theDialog.appendChild(formPane);
	theDialog.appendChild(textToElem(symbols[disj].letter, "div", false));
	entryField = makeMathField();
	entryField.style.marginTop = "0.66em";
	theDialog.appendChild(entryField);
	var okCancelPanel = makeButtonPanel(["OK", "Cancel"]);
	okCancelPanel.style.marginTop = "1.25em";
	theDialog.appendChild(okCancelPanel);
	okButton = okCancelPanel.firstChild;
	var cancelButton = okButton.nextSibling;
	okButton.onclick = finishAddition;
	cancelButton.onclick = function() {hideDialog()};
	entryField.oninput = setOKButton;
	showDialog(theDialog, okButton, true);
	entryField.focus();
	setOKButton();
}

function doDisjSyll() {
	var numSelected, firstGiven, firstData, disjVariant, disjForm, disjIndex;
	var disjuncts, numDisj, i, j, usedStmnts, infForm, infStmnt, stillToProve;
	var goalStmnt, goalForm, s;

	helpURL = "help/DisjSyll.html";
	commandName = "Disjunctive Syllogism";
	numSelected = selection.length;
	if (numSelected < 2) {
		useError();
		return;
	}
	firstData = getData(selection[0].parentNode);
	if (firstData.kind == defineGoal) {
		useError();
		return;
	} else if (firstData.kind == given) {
		firstGiven = 0;
	} else {
		firstGiven = 1;
	}
	findDisj: for (disjIndex = firstGiven; disjIndex < numSelected; disjIndex++) {
		if (disjIndex > firstGiven) {
			selection[firstGiven] = selection[disjIndex];
			selection[disjIndex] = disjVariant;
		}
		disjVariant = selection[firstGiven];
		disjForm = getForm(disjVariant);
		if (disjForm.kind == disj) {
			disjuncts = disjForm.args.slice(0);
			numDisj = disjuncts.length;
			matchGivens: for (j = firstGiven + 1; j < numSelected; j++) {
				var givenForm = getForm(selection[j]);
				for (i = 0; i < numDisj; i++) {
					if (formMatch(givenForm, disjuncts[i], false)) {
						disjuncts.splice(i, 1);
						numDisj--;
						continue matchGivens;
					}
				}
				// jth given didn't match, so this disjunction no good. Try next.
				continue findDisj;
			}
			// All givens match.  Use this disjunction.
			if (numDisj == 0) {
				useError();
				return;
			}
			usedStmnts = [];
			for (i = firstGiven; i < numSelected; i++) {
				s = getData(selection[i].parentNode).theStmnt;
				if (!usedStmnts.includes(s)) {
					usedStmnts.push(s);
				}
			}
			if (firstGiven == 0) {
				if (numDisj == 1) {
					infForm = disjuncts[0].cloneForm();
					infForm.parens = null;
				} else {
					for (i = 0; i < numDisj; i++) {
						disjuncts[i] = disjuncts[i].cloneForm();
					}
					infForm = new MultiCompoundFormula(disj, bool, disjuncts);
				}
				infStmnt = makeStmnt(infForm);
				forwardStep(selectedStep, null, usedStmnts, null, [infStmnt], null, false);
				return;
			} 
			// goal selected
			goalStmnt = firstData.theStmnt;
			if (goalStmnt == null) {
				useError();
				return;
			}
			goalForm = goalStmnt[getData(selection[0]).variant].theForm;
			if (!cutFromList(goalForm, disjuncts, disj)) {
				useError();
				return;
			}
			numDisj = disjuncts.length;
			if (numDisj == 0) {
				stillToProve = null;
			} else {
				stillToProve = [];
				for (j = 0; j < numDisj; j++) {
					s = makeStmnt(negate(disjuncts[j].cloneForm()));
					stillToProve.push(s);
					usedStmnts.push(s);
				}
			}
			backwardStep(selectedStep, null, stillToProve, usedStmnts, null);
			return;
		}
	}
	useError();
	return;
}

function doReflexive() {
	var numSel, entryField, okButton;

	function makeRefHTML(str) {
		return "By the reflexivity of equality, " +
			textToElemHTML(str, "span", true) + ".";
	}

	function afterError() {
		entryField.focus();
	}

	function finishRef() {
		var entry = parse(entryField, set);
		if (entry == null) {
			return;
		}
		if (!checkDefined(getData(selectedStep).defined, entry, afterError)) {
			return;
		}
		hideDialog();
		var infForm = new CompoundFormula(equals, bool, entry, entry.cloneForm());
		var infFWT = {theForm: infForm, theText: infForm.toText()};
		forwardStep(selectedStep, null, null, null, [[infFWT]], makeRefHTML(infFWT.theText), false);
	}

	function setOKButton() {
		okButton.disabled = (entryField.childNodes.length == 0);
	}

	helpURL = "help/Reflexive.html";
	commandName = "Reflexive Law";
	numSel = selection.length;
	if (!gapSelected(false) || (numSel > 1)) {
		useError();
		return;
	}
	if (numSel == 1) {
		var selData = getData(selection[0].parentNode);
		if (selData.kind == given) {
			useError();
			return;
		}
		if (selData.kind == goal) {
			var selStmnt = selData.theStmnt;
			if (selStmnt != null) {
				var selForm = selStmnt[getData(selection[0]).variant].theForm;
				if ((selForm.kind == equals) && formMatch(selForm.left, selForm.right, true)) {
					backwardStep(selectedStep, null, null, null, makeRefHTML(selStmnt[0].theText));
					return;
				}
			}
		}
	}
	var theDialog = makeDialog(42);
	theDialog.appendChild(mathPal);
	var introPane = makeTextPane("Reflexive law: <span class='formula'><i>x</i>=<i>x</i></span>.",
		1.25, 0.66);
	introPane.style.textAlign = "center";
	theDialog.appendChild(introPane);
	theDialog.appendChild(makeTextPane("Choose a value for <span class='formula'><i>x</i></span>:",
		0, 0.66));
	entryField = makeMathField();
	theDialog.appendChild(entryField);
	var okCancelPanel = makeButtonPanel(["OK", "Cancel"]);
	okCancelPanel.style.marginTop = "1.25em";
	theDialog.appendChild(okCancelPanel);
	okButton = okCancelPanel.firstChild;
	var cancelButton = okButton.nextSibling;
	okButton.onclick = finishRef;
	cancelButton.onclick = function() {hideDialog()};
	entryField.oninput = setOKButton;
	showDialog(theDialog, okButton, true);
	setOKButton();
	entryField.focus();
}
