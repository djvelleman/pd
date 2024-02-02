//Edit menu commands
"use strict";

function doFinish() {
  var goalStatement, numSelected, selectedGiven, selectedForm;
  var selectedGiven2, selectedForm2, merged, reiterate, match;
  var i, j;
  helpURL = "help/Finish.html";
  commandName = "Finish";
  if (!gapSelected(true)) {
    useError();
    return;
  }
  goalStatement = getGoal(selectedStep);
  numSelected = selection.length;
  if (numSelected == 0) {
    useError();
    return;
  }
  var selectedData = getData(selection[0].parentNode);
  if (selectedData.kind != given) {
    useError();
    return;
  }
  selectedGiven = selectedData.theStmnt;
  selectedForm = selectedGiven[getData(selection[0]).variant].theForm;
	if (goalStatement == null) {
		// Goal is contradiction.
		if (numSelected != 2) {
			useError();
			return;
		}
    selectedGiven2 = getData(selection[1].parentNode).theStmnt;
    selectedForm2 = selectedGiven2[getData(selection[1]).variant].theForm;
    if (!formMatch(selectedForm, selectedForm2, false)) {
			useError();
			return;
		}
    backwardStep(selectedStep, null, null, [selectedGiven, selectedGiven2], null);
    return;
	}
  // Goal is not contradiction
  if (numSelected != 1) {
    useError();
    return;
  }
  match = false;
  var n = goalStatement.length;
  for (i = 0; i < n; i++) {
    if (formMatch(selectedForm, goalStatement[i].theForm, true)) {
      match = true;
      break;
    }
  }
  if (!match) {
    useError();
    return;
  }
  if (!formMatch(selectedGiven[0].theForm, goalStatement[0].theForm, true)) {
    backwardStep(selectedStep, null, null, [selectedGiven], null);
    return;
  }
  // Given matches goal exactly.  Do we need to reiterate?
  var theGap = selectedStep;
  prepareStep();
  var steps = theGap.parentNode;
  var afterGap = theGap.nextSibling;
  var beforeGap = theGap.previousSibling;
  steps.removeChild(theGap);
	if (selectedGiven == goalStatement) {
		merged = selectedGiven;
	} else {
		merged = cloneStmnt(selectedGiven);
		var givenSize = selectedGiven.length;
		var goalSize = goalStatement.length;
		for (i = 1; i < goalSize; i++) {
			var goalFWT = goalStatement[i];
			var goalForm = goalFWT.theForm;
			match = false;
			for (j = 0; j < givenSize; j++) {
				var givenForm = selectedGiven[j].theForm;
				if (formMatch(givenForm, goalForm, true)) {
					match = true;
					break;
				}
			}
			if (!match) {
				merged.push(cloneFormWithText(goalFWT));
			}
		}
    merge(getData(mainProof), mainProof, selectedGiven, goalStatement, merged);
	}
  reiterate = (afterGap == null); // this means *might* reiterate
  if (reiterate) {
    reiterate = (beforeGap == null);
    if (!reiterate) {
      var beforeData = getData(beforeGap);
      if (beforeData.kind == inference) {
        var beforeInf = beforeData.inferred;
        reiterate = (beforeInf == null) || (beforeInf.length != 1) || (beforeInf[0] != merged);
      } else if (beforeData.kind == goalGap) {
        var beforeGoal = getGoal(beforeGap);
        reiterate = (beforeGoal != merged);
      } else {
        reiterate = true;
      }
    }
  }
  if (reiterate) {
    var infTextHTML = "We already know that " + textToElemHTML(merged[0].theText, "span", true) +
      ", as required.";
    var inf = makeInference(null, [merged], [merged], infTextHTML);
    if (afterGap == null) {
      steps.appendChild(inf);
    } else {
      steps.insertBefore(inf, afterGap);
    }
  }
  gapRemoved(steps);
}

function doDelete() {
  var i, whereUsed;

  function showUsed() {
    hideDialog();
    clearSelection();
    toggleStepSelected(null, whereUsed);
    whereUsed.scrollIntoView({behavior: "smooth", block: "nearest"});  // Is this a good idea?  Check if visible before scrolling??
  }  

  helpURL = "help/Delete.html";
  commandName = "Delete";
  if (selectedStep == null) {
    useError();
    return;
  }
	var selSize = selection.length;
	if (selSize > 0) {
    var selPane = selection[0];
    if ((getData(selPane.parentNode).kind == given) || (getData(selPane).variant > 0)) {
      var selCopy = selection.slice(0);
      prepareStep();
      for (i = 0; i < selSize; i++) {
        selPane = selCopy[i];
        var ggPane = selPane.parentNode;
        if (getData(selPane).variant == 0) {
          ggPane.parentNode.removeChild(ggPane);
        } else {
          ggPane.removeChild(selPane);
        }
      }
      return;
    }
  }
  // Delete entire step--inference or gap.
  var nextStep = selectedStep.nextSibling;
  if (nextStep == null) {
    useError("You can't delete the last step of a proof or subproof.");
    return;
  }
  var nowKnown = [];
  addContext(selectedStep, null, nowKnown);
  var delAssert = null;
  var delDefine = null;
  var stepData = getData(selectedStep);
  if (stepData.kind == inference) {
    delAssert = [];
    var inf;
    for (inf of stepData.inferred) { // Not null because contradiction is always last step
      if (!nowKnown.includes(inf)) {
        delAssert.push(inf);
      }
    }
    if (delAssert.length == 0) {
      delAssert = null;
    }
    delDefine = stepData.defined;
  } else if (stepData.kind == goalGap) {
    var theGoal = getGoal(selectedStep);
    if (!nowKnown.includes(theGoal)) {
      delAssert = [theGoal];
    }
  } else if (stepData.kind == defineGoalGap) {
    delDefine = [getDefineGoal(selectedStep)];
  }
  if ((delAssert != null) || (delDefine != null)) {
    var delAssertCopy = (delAssert == null) ? null : delAssert.slice(0);
    whereUsed = firstUse(nextStep, delDefine, delAssertCopy);
    if (whereUsed != null) {
      var msg = "This step can't be removed, because it is used later.<br><br>" +
      "<button id='show-used'>Show Where Used</button>";
      showMessage(msg);
      document.getElementById("show-used").onclick = showUsed;
      return;
    }
  }
  // Ready to delete.
  var removeGap = false;
  if (stepData.kind == inference) {
    if (stepData.subproofs != noSubproofs) {
      var c = selectedStep.childNodes;
      var pfRange = getProofRange(selectedStep);
      for (i = pfRange.first; i <= pfRange.last; i++) {
        if (!c[i].firstChild.classList.contains("complete")) {
          removeGap = true;
          break;
        }
      }
    }
  } else {
    removeGap = true;
  }
  var toDelete = selectedStep;
  var stepsPane = toDelete.parentNode;
  prepareStep();
  stepsPane.removeChild(toDelete);
  if ((delAssert != null) || (delDefine != null)) {
    deleteContext(nextStep, delDefine, delAssert);
  }
  if (removeGap) {
    gapRemoved(stepsPane);
  }
}

function doInsert() {
  var okButton, noGoalRadio, goalRadio, defineRadio, goalField, defineField, lemmaCheck;

  function setOKButton() {
    if (noGoalRadio.checked) {
      okButton.disabled = false;
    } else if (goalRadio.checked) {
      okButton.disabled = (goalField.childNodes.length == 0);
    } else if (defineRadio.checked) {
      okButton.disabled = (defineField.childNodes.length == 0);
    } else {
      okButton.disabled = true;
    }
  }

  function afterError() {
    if (goalRadio.checked) {
      goalField.focus();
    } else {
      defineField.focus();
    }
  }

  function finishInsert() {
    var insertion;
    var newGivens = null;
    var newDefined = null;
    if (noGoalRadio.checked) {
      insertion = makeNoGoalGap(nowDefined, nowKnown);
    } else if (goalRadio.checked) {
			var newGoalForm = parse(goalField, bool);
      if (newGoalForm == null) {
        return;
      }
      if (!checkDefined(nowDefined, newGoalForm, afterError)) {
        return;
      }
      var newGoal = makeStmnt(newGoalForm);
      newGivens = [newGoal];
      insertion = makeGoalGap(nowDefined, nowKnown, newGoal);
      if (lemmaCheck.checked) {
        insertion = makeLemma(newGoal, insertion, getProof(selectedStep));
      }
    } else { // defineRadio checked
      var theVar = getNewVar(defineField, nowDefined, willDefine, afterError);
      if (theVar == null) {
        return;
      }
      newDefined = [theVar];
      insertion = makeDefineGoalGap(nowDefined, nowKnown, theVar);
    }
    hideDialog();
    var insBefore = selectedStep;
    var steps = insBefore.parentNode;
    prepareStep();
    steps.insertBefore(insertion, insBefore);
    updateRest(insBefore, newDefined, newGivens);
    gapAdded(steps);
  }

  helpURL = "help/Insert.html";
  commandName = "Insert";
  if ((selectedStep == null) || (selection.length > 0)) {
    useError();
    return;
  }
  var nowDefined = [];
  var nowKnown = [];
  addContext(selectedStep, nowDefined, nowKnown);
  var willDefine = willBeDefined(selectedStep, true);
  var theDialog = makeDialog(42);
  theDialog.appendChild(mathPal);
  var noGoalGroup = makeRadioGroup("No goal", setOKButton, false);
  noGoalRadio = noGoalGroup.firstChild.firstChild;
  var goalGroup = makeRadioGroup("Prove:", setOKButton, true);
  goalRadio = goalGroup.firstChild.firstChild;
  goalField = goalGroup.lastChild;
  lemmaCheck = document.createElement("INPUT");
  lemmaCheck.type = "checkbox";
  var lemmaLabel = document.createElement("SPAN");
  lemmaLabel.innerHTML = "Lemma";
  lemmaLabel.style.marginLeft = radioCheckSpace + "em";
  var lemmaPanel = document.createElement("LABEL");
  lemmaPanel.style.marginLeft = "1.5em";
  lemmaPanel.appendChild(lemmaCheck);
  lemmaPanel.appendChild(lemmaLabel);
  goalGroup.insertBefore(lemmaPanel, goalField);
  var defineGroup = makeRadioGroup("Define:", setOKButton, true);
  defineRadio = defineGroup.firstChild.firstChild;
  defineField = defineGroup.lastChild;
  defineField.style.width = varFieldWidth + "em";
  noGoalGroup.style.marginTop = "1.25em";
  theDialog.appendChild(noGoalGroup);
  theDialog.appendChild(goalGroup);
  theDialog.appendChild(defineGroup);
  var okCancelPanel = makeButtonPanel(["OK", "Cancel"]);
  okButton = okCancelPanel.firstChild;
  var cancelButton = okButton.nextSibling;
  okButton.onclick = finishInsert;
  cancelButton.onclick = function() {hideDialog()};
  theDialog.appendChild(okCancelPanel);
  showDialog(theDialog, okButton, true);
  goalRadio.check = true;
  goalField.focus();
  setOKButton();
}

function doRejustify() {
  helpURL = "help/Rejustify.html";
  commandName = "Rejustify";
  if (selectedStep == null) {
    useError();
    return;
  }
  var selectedInf = selectedStep;
  var infData = getData(selectedStep);
  if (infData.kind != inference) {
    useError();
    return;
  }
  prepareStep();
  var steps = selectedInf.parentNode;
  var nowDefined = [];
  var nowKnown = [];
  addContext(selectedInf, nowDefined, nowKnown);
  var toDefine = infData.defined;
  var toProve = infData.inferred;
  var defined, numToDefine, nextToDefine, numToProve, nextToProve, g, i;
  if (toDefine != null) {
    numToDefine = toDefine.length;
    for (i = 0; i < numToDefine; i++) {
      nextToDefine = toDefine[i];
      defined = nowDefined.slice(0);
      g = makeDefineGoalGap(defined, nowKnown, nextToDefine);
      steps.insertBefore(g, selectedInf);
      nowDefined.push(nextToDefine);
    }
  }
  if (toProve != null) {
    numToProve = toProve.length;
    for (i = 0; i < numToProve; i++) {
      nextToProve = toProve[i];
      defined = nowDefined.slice(0);
      g = makeGoalGap(defined, nowKnown, nextToProve);
      steps.insertBefore(g, selectedInf);
      addElemToSet(nowKnown, nextToProve);
    }
  } else {
    steps.insertBefore(makeGoalGap(nowDefined, nowKnown, null), selectedInf);
  }
  steps.removeChild(selectedInf);
  gapAdded(steps);
}

function doLemma() {
  helpURL = "help/Lemma.html";
  commandName = "Lemma";
	if (!gapSelected(true)) {
		useError();
		return;
	}
	var goalStmnt = getGoal(selectedStep);
	if (goalStmnt == null) {
		useError();
		return;
	}
	var numSelected = selection.length;
	if (((numSelected == 1) && (getVarKind(selection[0]) == given)) ||
			(numSelected > 1)) {
		useError();
		return;
	}
  var theGap = selectedStep;
  prepareStep();
  var lemmaGap = updateGoalGap(theGap, null, null, goalStmnt);
  theGap.parentNode.replaceChild(makeLemma(goalStmnt, lemmaGap, getProof(theGap)), theGap);
}

function makeLemma(lemmaStmnt, lemmaGap, proof) {
  var i, infTextHTML;
  var depth = getData(proof).lemmaDepth;
  if (depth == 0) {
    infTextHTML = "Lemma. ";
  } else {
    infTextHTML = "Sub";
    for (i = 1; i < depth; i++) {
      infTextHTML += "sub";
    }
    infTextHTML += "lemma. ";
  }
  infTextHTML += textToElemHTML(lemmaStmnt[0].theText, "span", true) + ".";
  var theInference = makeInference(null, null, [lemmaStmnt], infTextHTML);
  var subpf = makeSubproof(null, null, lemmaStmnt, "", depth + 1, "Proof:");
  theInference.appendChild(subpf);
  getData(theInference).subproofs = subproofsLast;
  subpf.lastChild.appendChild(lemmaGap);
  return theInference;
}
