//Quantifier rules
"use strict";

function doArbEI(arb) {
  var theGap, gapData, oldVariant, instForm, instFormText, oldVar, selectedStmnt;
  var theVar, newVars, varListHTML, newStmnts, avoidVars, willDefine, newDefined;
  var arbEIDialog, formulaPane, varField, okButton, cancelButton, nextButton;

  function doOKNext(ok) {
    function afterError() {
      varField.focus();
      selectWholeField(varField);
    }

    if (varField.childNodes.length != 0) {
      theVar = getNewVar(varField, newDefined, willDefine, afterError);
      if (theVar == null) {
        return;
      }
      newVars.push(theVar);
      newDefined.push(theVar);
      handleVar();
      if (!ok) {
        formulaPane.innerHTML = textToHTML(instFormText, true);
        varField.focus();
        setUpVar();
        return;
      }
    }
    // OK clicked.  Do the edit.
    hideDialog();
    var newStatement = [{theForm: instForm, theText: instFormText}];
    var infTextHTML, subTextHTML;
    varListHTML = addVarListHTML("", newVars);
    if (arb) {
      if (newStmnts.length == 0) {
        newStmnts = null;
      }
      infTextHTML = "Since " + varListHTML;
      if (newVars.length > 1) {
        infTextHTML += " were";
      } else {
        infTextHTML += " was";
      }
      infTextHTML += " arbitrary, we can conclude that " + textToElemHTML(getGoal(theGap)[0].theText, "span", true) + ".";
      subTextHTML = "Let " + varListHTML + " be arbitrary.";
      if (newStmnts != null) {
        subTextHTML = addStmntListHTML(subTextHTML + " Suppose ", newStmnts) + ".";
      }
      prepareStep();
      var theInference = inferenceBySubproof(theGap,
          null, newVars, newStmnts, newStatement, infTextHTML, subTextHTML, true);
      theGap.parentNode.replaceChild(theInference, theGap);
    } else {  // EI
      newStmnts.unshift(newStatement);
      selectedStmnt = getData(selection[0].parentNode).theStmnt;
      forwardStep(theGap, null, [selectedStmnt], newVars, newStmnts, makeEIInfTextHTML(),
          (gapData.kind == defineGoalGap) && newVars.includes(getDefineGoal(theGap)));
    }    
  }

  function handleVar() {
    addElemToSet(avoidVars, theVar);
    var scope = instForm.scope.plugIn(oldVar, theVar, avoidVars, true);
    var bound = instForm.from;
    var newGiven;
    if (bound != null) {
      bound.parens = null;
      newGiven = new CompoundFormula(element, bool, new AtomicTerm(theVar), bound);
      newStmnts.push(makeStmnt(newGiven));
    }
    if (instForm.kind == unique) {
      if (bound != null) {
        bound = bound.cloneForm();
      }
      newGiven = scope.cloneForm();
      newGiven = newGiven.assertUnique(1, theVar, bound, avoidVars, true);
      newStmnts.push(makeStmnt(newGiven));
    }
    instForm = scope;
    instFormText = instForm.toText();
  }

  function makeEIInfTextHTML() {
    return addStmntListHTML("Since " + textToElemHTML(selectedStmnt[0].theText, "span", true) +
      ", we can choose " + varListHTML + " such that ", newStmnts) + ".";
  }

  function setUpVar() {
    oldVar = instForm.bdVar;
    if (newDefined.includes(oldVar) || (!arb && willDefine.includes(oldVar))) {
      removeAllInput(varField);
    } else {
      varField.innerHTML = textToHTML(varToText(oldVar));
    }
    selectWholeField(varField);
    setButtons();
  }

  function setButtons() {
    var input = (varField.childNodes.length != 0);
    okButton.disabled = (!input && (newVars.length == 0));
    var disableNext;
    var scopeKind = instForm.scope.kind;
    if (arb) {
      disableNext = (scopeKind != all);
    } else {
      disableNext = ((scopeKind != exist) && (scopeKind != unique));
    }
    nextButton.disabled = (!input || disableNext);
  }

  // Start of doArbEI
  if (arb) {
    helpURL = "help/Arbitrary.html";
    commandName = "Arbitrary Object";
  } else {
    helpURL = "help/EI.html";
    commandName = "Existential Instantiation";
  }
  if (!gapSelected(arb)) {
    useError();
    return;
  }
  if (!arb && (selection.length == 2)) {
    var goalData = getData(selection[0].parentNode);
    if (goalData.kind != defineGoal) {
      useError();
      return;
    }
    theVar = goalData.toDef;
    selectedStmnt = getData(selection[1].parentNode).theStmnt;
    oldVariant = selectedStmnt[getData(selection[1]).variant];
    instForm = oldVariant.theForm;
    if ((instForm.kind != exist) && (instForm.kind != unique)) {
      useError();
      return;
    }
    instForm = instForm.cloneForm();
    avoidVars = getData(selectedStep).defined.slice(0);
    instForm.addVars(avoidVars, false);
    oldVar = instForm.bdVar;
    newStmnts = [];
    handleVar();
    newStmnts.unshift([{theForm: instForm, theText: instFormText}])
    varListHTML = textToElemHTML(varToText(theVar), "span", false);
    forwardStep(selectedStep, null, [selectedStmnt], [theVar], newStmnts, makeEIInfTextHTML(), true);
    return;
  }
  if (arb) {
    oldVariant = getGoalVariant(all, true);
  } else {
    oldVariant = getGivenVariant(anyKind);
    if (oldVariant != null) {
      var k = oldVariant.theForm.kind;
      if ((k != exist) && (k != unique)) {
        oldVariant = null;
      }
    }
  }
  if (oldVariant == null) {
    useError();
    return;
  }
  theGap = selectedStep;
  gapData = getData(theGap);
  instForm = oldVariant.theForm.cloneForm();
  instFormText = oldVariant.theText;
  newVars = [];
  newStmnts = [];
  newDefined = gapData.defined.slice(0);
  avoidVars = newDefined.slice(0);
  instForm.addVars(avoidVars, false);
  arbEIDialog = makeDialog(32);
  formulaPane = textToElem(instFormText, "div", true);
  formulaPane.style.height = (2 * lineHeight) + "em";
  arbEIDialog.appendChild(formulaPane);
  var prompt;
  if (arb) {
    prompt = "Choose a variable to stand for an arbitrary object:";
    willDefine = null;
  } else {
    prompt = "Choose a variable to stand for the object that is asserted to exist:";
    willDefine = willBeDefined(theGap, false);
    addSetToSet(avoidVars, willDefine);
  }
  var promptPane = makeTextPane(prompt, 0.66, 0);
  promptPane.style.textAlign = "center";
  arbEIDialog.appendChild(promptPane);
  varField = makeMathField();
  varField.style.width = varFieldWidth + "em";
  varField.style.margin = "1.25em auto 1.25em";
  arbEIDialog.appendChild(varField);
  var buttonPane = makeButtonPanel(["OK", "Cancel", "Next"]);
  arbEIDialog.appendChild(buttonPane);
  okButton = buttonPane.firstChild;
  cancelButton = okButton.nextSibling;
  nextButton = cancelButton.nextSibling;
  okButton.onclick = function() {doOKNext(true)};
  cancelButton.onclick = function() {hideDialog()};
  nextButton.onclick = function() {doOKNext(false)};
  varField.oninput = setButtons;
  showDialog(arbEIDialog, okButton, true);
  varField.focus();
  setUpVar();
}

function doExistUI(ex) {
  var gapData, ggData, qfiedForm, qfiedStmnt;
  var qfiedFWT = null;
  var instForm, instFormText, oldVar;
  var qfiedSelection, i, numSelected;
  var newVars, boundForms, newStmnt;
  var avoidVars, willDefine, newDefined;
  var existUIDialog, formulaPane, promptPane, promptStart, promptFinish;
  var valueGroup, variableGroup, valueButton, variableButton, valueField, variableField;
  var okButton, cancelButton, nextButton, didOne;

  function doOKNext(ok) {
    var inputField, theTerm;

    function afterError() {
      inputField.focus();
    }

    if (valueButton.checked) {
      inputField = valueField;
    } else {
      inputField = variableField;
    }
    if (inputField.childNodes.length != 0) {
      var bound = instForm.from;
      var scope = instForm.scope;
      if (valueButton.checked) {
        theTerm = parse(valueField, set);
        if (theTerm == null) {
          return;
        }
        if (!checkDefined(newDefined, theTerm, afterError)) {
          return;
        }
        theTerm.addVars(avoidVars, false);
        scope = scope.plugIn(oldVar, theTerm, avoidVars, true);
      } else {
        var theVar = getNewVar(variableField, newDefined, willDefine, afterError);
        if (theVar == null) {
          return;
        }
        newVars.push(theVar);
        newDefined.push(theVar);
        addElemToSet(avoidVars, theVar);
        scope = scope.plugIn(oldVar, theVar, avoidVars, true);
        if (bound != null) {
          theTerm = new AtomicTerm(theVar);
        }
      }
      if (bound != null) {
        bound.parens = null;
        boundForms.push(new CompoundFormula(element, bool, theTerm, bound));
      }
      instForm = scope;
      instFormText = instForm.toText();
      if (!ok) {
        didOne = true;
        formulaPane.innerHTML = textToHTML(instFormText);
        initVar();
        return;
      }
    }
    // OK clicked.  Do step.
    if (newVars.length == 0) {
      newVars = null;
    }
    hideDialog();
		if (ex) {
      var i;
      var n = boundForms.length;
      for (i = 0; i < n; i++) {
        boundForms[i] = makeStmnt(boundForms[i]);
      }
      boundForms.push([{theForm: instForm, theText: instFormText}]);
      backwardStep(selectedStep, newVars, boundForms, boundForms, null);
		} else {
			if (boundForms.length == 0) {
				newStmnt = [{theForm: instForm, theText: instFormText}];
			} else {
				var newForm;
				if (boundForms.length == 1) {
					newForm = boundForms[0];
				} else {
					newForm = new MultiCompoundFormula(conj, bool, boundForms);
				}
				newForm = new CompoundFormula(cond, bool, newForm, instForm);
				newStmnt = makeStmnt(newForm);
			}
			forwardStep(selectedStep, newVars, [qfiedStmnt], null, [newStmnt], null, false);
		}
  }

  function initVar() {
    oldVar = instForm.bdVar;
    var varText = varToText(oldVar);
    promptPane.innerHTML = promptStart +
        textToElemHTML(varText, "span", false) + promptFinish;
    removeAllInput(valueField);
    if (newDefined.includes(oldVar) || willDefine.includes(oldVar)) {
      removeAllInput(variableField);
    } else {
      variableField.innerHTML = textToHTML(varText);
    }
    valueButton.checked = true;
    valueField.focus();
    setButtons();
  }

  function setButtons() {
    var input = ((valueButton.checked && (valueField.childNodes.length != 0)) ||
        (variableButton.checked && (variableField.childNodes.length != 0)));
    okButton.disabled = !(input || didOne);
    var desiredKind = ex ? exist : all;
    nextButton.disabled = !(input && (instForm.scope.kind == desiredKind));
  }

  // Start of doExistUI
  if (ex) {
    helpURL = "help/Existence.html";
    commandName = "Existence";
  } else {
    helpURL = "help/UI.html";
    commandName = "Universal Instantiation";
  }
  numSelected = selection.length;
  if (!gapSelected(ex) || (numSelected > 2)) {
    useError();
    return;
  }
  gapData = getData(selectedStep);
  if (ex) {
    qfiedFWT = getGoalVariant(exist, false);
    qfiedSelection = 0;
  } else {
    for (i = 0; i < numSelected; i++) {
      ggData = getData(selection[i].parentNode);
      if (ggData.kind != given) {
        useError();
        return;
      }
      qfiedStmnt = ggData.theStmnt;
      var selFWT = qfiedStmnt[getData(selection[i]).variant];
      if (selFWT.theForm.kind == all) {
        qfiedSelection = i;
        qfiedFWT = selFWT;
        break;
      }
    }
  }
  if (qfiedFWT == null) {
    useError();
    return;
  }
  qfiedForm = qfiedFWT.theForm;
	if (numSelected == 2) {   //Use 2nd selected given to decide what to instantiate.
		var selElem = selection[1 - qfiedSelection];
		var elemStmnt = getData(selElem.parentNode).theStmnt;
		var elemForm = elemStmnt[getData(selElem).variant].theForm;
		if ((qfiedForm.from == null) || (elemForm.kind != element) ||
				!formMatch(qfiedForm.from, elemForm.right, true)) {
			useError();
			return;
		}
    avoidVars = willBeDefined(selectedStep, true);
		var newTerm = elemForm.left;
		addSetToSet(avoidVars, gapData.defined);
		qfiedForm.addVars(avoidVars, false);
		newTerm.addVars(avoidVars, false);
		var newForm = qfiedForm.scope.cloneForm().plugIn(qfiedForm.bdVar, newTerm, avoidVars, false);
		newStmnt = makeStmnt(newForm);
		if (ex) {
      backwardStep(selectedStep, null, [newStmnt], [elemStmnt, newStmnt], null);
		} else {
      forwardStep(selectedStep, null, [elemStmnt, qfiedStmnt], null, [newStmnt], null, false);
		}
	} else {   //Do dialog to decide what to instantiate.
    instForm = qfiedForm.cloneForm();
    instFormText = qfiedFWT.theText;
    newVars = [];
    boundForms = [];
    willDefine = willBeDefined(selectedStep, true);
    avoidVars = willDefine.slice(0);
    newDefined = gapData.defined.slice(0);
    addSetToSet(avoidVars, newDefined);
    instForm.addVars(avoidVars, false);
    existUIDialog = makeDialog(42);
    existUIDialog.appendChild(mathPal);
    formulaPane = textToElem(instFormText, "div", true);
    formulaPane.style.height = (2 * lineHeight) + "em";
    formulaPane.style.marginTop = "0.66em";
    existUIDialog.appendChild(formulaPane);
    promptPane = makeTextPane(textToElemHTML("x", "span", false), 0.66, 0.66); // Placeholder until correct prompt filled in
    promptPane.style.textAlign = "center";
    existUIDialog.appendChild(promptPane);
    valueGroup = makeRadioGroup("Use this value:", setButtons, true);
    valueButton = valueGroup.firstChild.firstChild;
    valueField = valueGroup.lastChild;
    existUIDialog.appendChild(valueGroup);
    variableGroup = makeRadioGroup("Use this new variable, whose definition will be inserted later:", setButtons, true);
    variableButton = variableGroup.firstChild.firstChild;
    variableField = variableGroup.lastChild;
    variableField.style.width = varFieldWidth + "em";
    existUIDialog.appendChild(variableGroup);
    var buttonPane = makeButtonPanel(["OK", "Cancel", "Next"]);
    buttonPane.style.marginTop = "0.66em";
    existUIDialog.appendChild(buttonPane);
    okButton = buttonPane.firstChild;
    cancelButton = okButton.nextSibling;
    nextButton = cancelButton.nextSibling;
    okButton.onclick = function() {doOKNext(true)};
    cancelButton.onclick = function() {hideDialog()};
    nextButton.onclick = function() {doOKNext(false)};
    didOne = false;
    if (ex) {
      promptStart = "What value should be substituted for ";
      promptFinish = " to make the goal true?";
    } else {
      promptStart = "What would you like to substitute for ";
      promptFinish = "?";
    }
    showDialog(existUIDialog, okButton, true);
    initVar();
  }
}
