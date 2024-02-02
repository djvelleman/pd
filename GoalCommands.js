// Goal menu commands
"use strict";

function doDirContrap(doDirect) {
  if (doDirect) {
    helpURL = "help/Direct.html";
    commandName = "Direct";
  } else {
    helpURL = "help/Contrapos.html";
    commandName = "Contrapositive";
  }
  if (!gapSelected(true)) {
    useError();
    return;
  }
  var theGap = selectedStep;
  var goalVariant = getGoalVariant(cond, true);
  if (goalVariant == null) {
    useError();
    return;
  }
  prepareStep();
  var conditional = goalVariant.theForm;
	var newGivenFormula, newGoalFormula;
	if (doDirect) {
		newGivenFormula = conditional.left.cloneForm();
		newGoalFormula = conditional.right.cloneForm();
		newGivenFormula.parens = null;
		newGoalFormula.parens = null;
	} else {
		newGivenFormula = negate(conditional.right.cloneForm());
    newGoalFormula = negate(conditional.left.cloneForm());
  }
  var newGiven = makeStmnt(newGivenFormula);
  var newGoal = makeStmnt(newGoalFormula);
  var theInference = inferenceBySubproof(theGap, null, null, [newGiven], newGoal, null, null, true);
  theGap.parentNode.replaceChild(theInference, theGap);
}

function doBicond() {
  helpURL = "help/Bicond.html";
  commandName = "Biconditional";
  if (!gapSelected(true)) {
    useError();
    return;
  }
	var goalVariant = getGoalVariant(bicond, true);
	if (goalVariant == null) {
		useError();
		return;
	}
  var theGap = selectedStep;
  prepareStep();
	var biconditional = goalVariant.theForm;
	var leftSide = biconditional.left;
	var rightSide = biconditional.right;
	var ltor = new CompoundFormula(cond, bool, leftSide.cloneForm(), rightSide.cloneForm());
	var rtol = new CompoundFormula(cond, bool, rightSide.cloneForm(), leftSide.cloneForm());
	var theInference = inferenceBySubproof(theGap, null, null, null,
		makeStmnt(ltor), null, "\u2192:", true);
	var firstSubpf = theInference.firstChild;
  var rtolStmnt = makeStmnt(rtol);
  var subpfData = getData(firstSubpf);
	var nextSubpf = makeSubproof(null, null, rtolStmnt, subpfData.casePrefix,
		subpfData.lemmaDepth, "\u2190:");
  nextSubpf.lastChild.appendChild(updateGoalGap(theGap, null, null, rtolStmnt));
  theInference.insertBefore(nextSubpf, firstSubpf.nextSibling);
  theGap.parentNode.replaceChild(theInference, theGap);
}


function doConj(conjoin) {
  var usedStmnts, stillToProve, conjuncts, varPane, backwards, numSelected, i, s;
  if (conjoin) {
    helpURL = "help/Conjoin.html";
    commandName = "Conjoin";
  } else {
    helpURL = "help/Conjunction.html";
    commandName = "Conjunction";
  }
  usedStmnts = [];
  numSelected = selection.length;
  backwards = ((numSelected == 0) || (getVarKind(selection[0]) != given));
  if (!gapSelected(backwards)) {
    useError();
    return;
  }
  if (backwards) {
    if (conjoin && (numSelected <= 1)) {
      useError();
      return;
    }
    var conjFWT = getGoalVariant(conj, false);
    if (conjFWT == null) {
      useError();
      return;
    }
    conjuncts = conjFWT.theForm.args.slice(0);
    for (i = 1; i < numSelected; i++) {
      varPane = selection[i];
      s = getData(varPane.parentNode).theStmnt;
      if (!cutFromList(s[getData(varPane).variant].theForm, conjuncts, conj)) {
        useError();
        return;
      }
      if (!usedStmnts.includes(s)) {
        usedStmnts.push(s);
      }
    }
    var numConjuncts = conjuncts.length;
    if (numConjuncts == 0) {
      stillToProve = null;
    } else {
      stillToProve = [];
      for (i = 0; i < numConjuncts; i++) {
        var concForm = conjuncts[i].cloneForm();
        concForm.parens = null;
        s = makeStmnt(concForm);
        stillToProve.push(s);
        usedStmnts.push(s);
      }
    }
    backwardStep(selectedStep, null, stillToProve, usedStmnts, null);
  } else {
    if (!conjoin || (numSelected == 1)) {
      useError();
      return;
    }
    conjuncts = [];
    for (i = 0; i < numSelected; i++) {
      varPane = selection[i];
      s = getData(varPane.parentNode).theStmnt;
      var givenForm = s[getData(varPane).variant].theForm.cloneForm();
      addToList(givenForm, conjuncts, conj);
      if (!usedStmnts.includes(s)) {
        usedStmnts.push(s);
      }
    }
    var infStmnt = makeStmnt(new MultiCompoundFormula(conj, bool, conjuncts));
    forwardStep(selectedStep, null, usedStmnts, null, [infStmnt], null, false);
  }
}

function doDisj() {
  var goalVariant, theDialog, disjPane, disjList, numDisjuncts, i;
  var okButton, negateBox;
  var selDisj = null;

  function selectDisj(e) {
    if (selDisj != null) {
      selDisj.classList.remove("selected");
    }
    selDisj = e;
    selDisj.classList.add("selected");
    okButton.disabled = false;
  }

  function finishDisj() {
    hideDialog();
    var theGap = selectedStep;
    prepareStep();
    var toProveFWT = getData(selDisj).formWithText;
    var toProveStmnt = [toProveFWT];
    if (negateBox.checked) {
      var newPremises = [];
      var nextPrem = disjPane.firstChild;
      do {
        if (nextPrem != selDisj) {
          newPremises.push(makeStmnt(negate(getData(nextPrem).formWithText.theForm)));
        }
        nextPrem = nextPrem.nextSibling;
      } while (nextPrem != null);
			var theInference = inferenceBySubproof(theGap, null, null, newPremises,
				toProveStmnt, null, null, true);
      theGap.parentNode.replaceChild(theInference, theGap);
    } else {
      backwardStep(theGap, null, [toProveStmnt], [toProveStmnt], null);
    }
  }

  helpURL = "help/Disjunction.html";
  commandName = "Disjunction";
  if (!gapSelected(true)) {
    useError();
    return;
  }
	goalVariant = getGoalVariant(disj, false);
	if (goalVariant == null) {
		useError();
		return;
	}
  if (selection.length > 2) {
    useError();
    return;
  }
  if (selection.length == 2) {
    finishByAddition(goalVariant.theForm);
    return;
  }
  theDialog = makeDialog(32);
  theDialog.appendChild(makeTextPane("Which statement are you going to prove?", 0, 0.66));
  disjPane = document.createElement("DIV");
  disjPane.className = "list-pane";
  disjPane.style.height = (6 * (lineHeight + 0.1)) + "em";
  theDialog.appendChild(disjPane);
  disjList = goalVariant.theForm.args;
  numDisjuncts = disjList.length;
  for (i = 0; i < numDisjuncts; i++) {
    var theDisj = disjList[i].cloneForm();
    theDisj.parens = null;
    var theDisjFWT = {theForm: theDisj, theText: theDisj.toText()};
    var elem = textToElem(theDisjFWT.theText, "DIV", false);
    var disjData = makeData(elem);
    disjData.formWithText = theDisjFWT;
    elem.onclick = function() {selectDisj(this)};
    elem.classList.add("list-element");
    elem.style.height = (lineHeight + 0.1) + "em";
    disjPane.appendChild(elem);
  }
  var negatePane = document.createElement("LABEL");
  negatePane.style.margin = "0.66em 0em 0.66em";
  negateBox = document.createElement("INPUT");
  negateBox.type = "checkbox";
  negateBox.checked = true;
  negatePane.appendChild(negateBox);
  var negateLabel = document.createElement("SPAN");
  negateLabel.innerHTML = "Assume negations of others.";
  negateLabel.style.marginLeft = radioCheckSpace + "em";
  negatePane.appendChild(negateLabel);
  theDialog.appendChild(negatePane);
  var okCancelPanel = makeButtonPanel(["OK", "Cancel"]);
  theDialog.appendChild(okCancelPanel);
  okButton = okCancelPanel.firstChild;
  var cancelButton = okButton.nextSibling;
  okButton.disabled = true;
  okButton.onclick = finishDisj;
  cancelButton.onclick = function() {hideDialog()};
  showDialog(theDialog, okButton, true);
}

function doExistUnique() {
  helpURL = "help/ExistUnique.html";
  commandName = "Existence & Uniqueness";
  if (!gapSelected(true)) {
    useError();
    return;
  }
  var goalVariant = getGoalVariant(unique, true);
	if (goalVariant == null) {
		useError();
		return;
	}
  var theGap = selectedStep;
  prepareStep();
	var existGoal = goalVariant.theForm.cloneForm();
	existGoal.kind = exist;
	var avoidVars = willBeDefined(theGap, false);
  addSetToSet(avoidVars, getData(theGap).defined);
	existGoal.addVars(avoidVars, false);
	var qScope = existGoal.scope.cloneForm();
	var qBound = existGoal.from;
	if (qBound != null) {
		qBound = qBound.cloneForm();
	}
  var uniqueGoal = qScope.assertUnique(2, existGoal.bdVar, qBound, avoidVars, false);
  var uniqueStmnt = makeStmnt(uniqueGoal);
  var theInference = inferenceBySubproof(theGap, null, null, null,
		makeStmnt(existGoal), null, "Existence", true);
  var firstSubpf = theInference.firstChild;
  var pfData = getData(firstSubpf);
  var nextSubpf = makeSubproof(null, null, uniqueStmnt,
    pfData.casePrefix, pfData.lemmaDepth, "Uniqueness");
  theInference.insertBefore(nextSubpf, firstSubpf.nextSibling);
  nextSubpf.lastChild.appendChild(updateGoalGap(theGap, null, null, uniqueStmnt));
  theGap.parentNode.replaceChild(theInference, theGap);
}

// goalForm is a disjunction, one given also selected.  See if we can finish by addition.
function finishByAddition(goalForm) {
  var givenStmnt = getData(selection[1].parentNode).theStmnt;
  var givenForm = givenStmnt[getData(selection[1]).variant].theForm;
  var goalArgs = goalForm.args.slice(0);
  if (!cutFromList(givenForm, goalArgs, disj) || (goalArgs.length == 0)) {
    useError();
  } else {
    backwardStep(selectedStep, null, null, [givenStmnt], null);
  }
}