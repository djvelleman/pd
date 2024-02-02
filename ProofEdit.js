// Utility functions for proof edits
"use strict";

/* gap must be a goalGap.  Returns an inference in which goal is inferred from
usedStmnts and a SubProof in which newDefined variables are introduced, newPremises are
assumed, and newConclusion is proven.  infText is text of inference; if null,
use default produced by createInference.  subText is intro text for SubProof; if null, use
"Suppose (newPremises)"; newPremises must be non-null for this.
Anything can be null except proofBefore.
*/ 
function inferenceBySubproof(gap, usedStmnts, newDefined, newPremises, newConclusion, infTextHTML, subTextHTML, proofBefore) {
  var thisProof = getProof(gap);
  var pfData = getData(thisProof);
  if (subTextHTML == null) {
    subTextHTML = supposeTextHTML(newPremises);
  }
  var goalStmnt = getGoal(gap);
  var theInference = makeInference(null, usedStmnts, (goalStmnt == null) ? null : [goalStmnt], infTextHTML);
  var theSubproof = makeSubproof(newDefined, newPremises, newConclusion, pfData.casePrefix, pfData.lemmaDepth, subTextHTML);
  if (proofBefore) {
    theInference.insertBefore(theSubproof, theInference.firstChild);
    getData(theInference).subproofs = subproofsFirst;
  } else {
    theInference.appendChild(theSubproof);
    getData(theInference).subproofs = subproofsLast;
  }
  theSubproof.lastChild.appendChild(updateGoalGap(gap, newDefined, newPremises, newConclusion));
  return theInference;
}

  /* Inserts before gap a sequence of gaps for
defining the variables in newVars, then inference of infStmnts and definition of definedVars
using usedStmnts, using infHTML or default text if infHTML is null.  If clearGap, remove Gap.
newVars, infStmnts, usedStmnts, definedVars, and infHTML can all be null.  (infStmnts null means
infer contradiction.)
*/
function forwardStep(gap, newVars, usedStmnts, definedVars, infStmnts, infHTML, clearGap) {
  prepareStep();
  var stepsPane = gap.parentNode;
  var newDefined;
  if (newVars != null) {
    addDefineGaps(stepsPane, gap, newVars);
    if (definedVars == null) {
      newDefined = newVars;
    } else {
      newDefined = definedVars.slice(0);
      addSetToSet(newDefined, newVars);
    }
  } else {
    newDefined = definedVars;
  }
  stepsPane.insertBefore(makeInference(definedVars, usedStmnts, infStmnts, infHTML), gap);
  var nextStep;
  if (clearGap) {
    nextStep = gap.nextSibling;
    stepsPane.removeChild(gap);
  } else {
    nextStep = gap;
  }
  if ((newDefined != null) || (infStmnts != null)) {
    updateRest(nextStep, newDefined, infStmnts);
  }
  if (clearGap && (newVars == null)) {
    gapRemoved(stepsPane);
  }
}

/* gap must be a goalGap.  Replace gap with sequence of gaps for
defining the variables in newVars, then sequence of gaps for proving the statements in stillToProve,
then inference of goal from usedStmnts, using infText or default text if infText is null.
newVars, stillToProve, usedStmnts, and infText can all be null.
*/
function backwardStep(gap, newVars, stillToProve, usedStmnts, infHTML) {
  prepareStep();
  var stepsPane = gap.parentNode;
  var i, g, s, last, numToProve;
  if (newVars != null) {
    g = addDefineGaps(stepsPane, gap, newVars);
    last = [newVars[newVars.length - 1]];
  } else {
    g = gap;
    last = null;
  }
  if (stillToProve != null) {
    numToProve = stillToProve.length;
    s = stillToProve[0];
    g = updateGoalGap(g, last, null, s);
    stepsPane.insertBefore(g, gap);
    last = [s];
    for (i = 1; i < numToProve; i++) {
      s = stillToProve[i];
      g = updateGoalGap(g, null, last, s);
      stepsPane.insertBefore(g, gap);
      last[0] = s;
    }
  }
  s = getGoal(gap);
  var nextStep = gap.nextSibling;
  stepsPane.replaceChild(makeInference(null, usedStmnts, (s == null) ? null : [s], infHTML), gap);
  if ((newVars == null) && (stillToProve == null)) {
    gapRemoved(stepsPane);
  } else {
    updateRest(nextStep, newVars, stillToProve);
  }
}

function addVariant(stmnt, newVariant) {
  prepareStep();
  stmnt.push(newVariant);
  addVariantToSteps(mainProof, stmnt);
}

function addVariantToSteps(stepsPane, stmnt) {
  function updateGG(gg) {
    if (getData(gg).theStmnt == stmnt) {
      gg.appendChild(makeVariantPane(textToElemHTML(stmnt[newVarNum].theText, "div", true), newVarNum));
    }
  }

  var c = stepsPane.childNodes;
  var n = c.length;
  var newVarNum, nextStep, i, j, c2, d, proofRange, detailsPane, numG;
  for (i = 0; i < n; i++) {
    nextStep = c[i];
    d = getData(nextStep);
    if (d.kind == inference) {
      if (d.subproofs != noSubproofs) {
        proofRange = getProofRange(nextStep);
        c2 = nextStep.childNodes;
        for (j = proofRange.first; j <= proofRange.last; j++) {
          addVariantToSteps(c2[j].lastChild, stmnt);
        }
      }
    } else { // Gap
      detailsPane = nextStep.firstChild.lastChild;
      newVarNum = stmnt.length - 1;
      numG = numGivens(d.kind, detailsPane);
      c2 = detailsPane.childNodes;
      for (j = 1; j <= numG; j++) {
        updateGG(c2[j]);
      }
      if (d.kind == goalGap) {
        updateGG(c2[c2.length - 1]);
      }
    }
  }
}

function addDefineGaps(stepsPane, gap, newVars) {
  var i;
  var numNewVar = newVars.length;
  var v = newVars[0];
  var g = updateDefineGap(gap, null, null, v);
  stepsPane.insertBefore(g, gap);
  var lastDefined = [v];
  for (i=1; i < numNewVar; i++) {
    v = newVars[i];
    g = updateDefineGap(g, lastDefined, null, v);
    stepsPane.insertBefore(g, gap);
    lastDefined[0] = v;
  }
  return g;
}

function gapSelected(requireGoal) {
  if (selectedStep == null) {
    return false;
  }
  var d = getData(selectedStep);
  return ((d.kind != inference) && (!requireGoal || (d.kind == goalGap)));
}


/* Only call this when selectedStep is a goalGap.  Return FormWithText for goal variant of required kind if
either Gap is selected, or variant of Goal is selected; if not, or if variant of required
kind not found, return null.  If desiredKind is anyKind, allow any kind of goal except
contradiction.  If noExtraSel, return null if anything other than goal variant is selected.
*/
function getGoalVariant(desiredKind, noExtraSel) {
	var selectedStmnt = getGoal(selectedStep);
	if (selectedStmnt == null) {
		return null;
	}
	var i, result;
	var numSelected = selection.length;
	if (numSelected > 0) {
		if (noExtraSel && (numSelected > 1)) {
			return null;
		}
    var selected = selection[0];
    if (getVarKind(selected) != goal) {
      return null;
    }
    result = selectedStmnt[getData(selected).variant];
		return ((desiredKind == anyKind) || (result.theForm.kind == desiredKind)) ?
			result : null;
	}
	if (desiredKind == anyKind) {
		return selectedStmnt[0];
	}
	var numVariant = selectedStmnt.length;
	for (i = 0; i < numVariant; i++) {
		result = selectedStmnt[i];
		if (result.theForm.kind == desiredKind) {
			return result;
		}
	}
	return null;
}

/* Return FormWithText for given variant of required kind if
variant of given is only selection; if not, or if variant is not of required kind, return null.
If desiredKind is Formula.anyKind, allow any kind.
*/
function getGivenVariant(desiredKind) {
	if (selection.length != 1) {
		return null;
	}
  var selected = selection[0];
  var ggPane = selected.parentNode;
  var ggData = getData(ggPane);
	if (ggData.kind != given) {
		return null;
	}
	var result = ggData.theStmnt[getData(selected).variant];
	return ((desiredKind == anyKind) || (result.theForm.kind == desiredKind)) ? result : null;
}

/* Make a copy of gap, with following changes:  Set kind as specified, add newDefined to
defined variables, add newPremises as new givens, and use introHTML as text of IntroPane.  Don't copy goal.
newDefined and newPremises can be null if no new defined variables or premises.
introHTML cannot be null.
*/
function updateGap(gap, kind, newDefined, newPremises, introHTML) {
  var d = getData(gap);
	var definedCopy = d.defined.slice(0);
	if (newDefined != null) {
		addSetToSet(definedCopy, newDefined);
  }
  var g = makeGapStruct(kind, definedCopy, introHTML)
  var origDetails = gap.firstChild.lastChild;
  var detailsPane = g.firstChild.lastChild;
  copyGivens(d.kind, origDetails, detailsPane, false);
  if (newPremises != null) {
    addGivens(detailsPane, newPremises);
  }
  return g;
}

/* As above, but set kind to goalGap, set conclusion as goal, and intro text is "Proof of (conclusion)
goes here".  conclusion null for contradiction.
*/
function updateGoalGap(gap, newDefined, newPremises, conclusion) {
	var g = updateGap(gap, goalGap, newDefined, newPremises, proofHereTextHTML(conclusion));
	addGoal(g.firstChild.lastChild, conclusion);
	return g;
}

/* As above, but set kind to defineGap, set toDef as variable to be defined, and intro text is
"Definition of (toDef) goes here".
*/
function updateDefineGap(gap, newDefined, newPremises, toDef) {
	var g = updateGap(gap, defineGoalGap, newDefined, newPremises, definitionHereTextHTML(toDef));
	addDefineGoal(g.firstChild.lastChild, toDef);
	return g;
}

function updateRest(step, newDefined, newGivens) {
  while (step != null) {
    updateContext(step, newDefined, newGivens);
    step = step.nextSibling;
  }

}

// Add newDefined and newGivens to gap or all contained gaps.
// newDefined and newGivens can be null.
function updateContext(step, newDefined, newGivens) {
  var d = getData(step);
  var i, c;
  if (d.kind == inference) {
    if (d.subproofs == noSubproofs) {
      return;
    }
    var proofRange = getProofRange(step);
    c = step.childNodes;
    var pfStep;
    for (i = proofRange.first; i <= proofRange.last; i++) {
      pfStep = c[i].lastChild.firstChild;
      do {
        updateContext(pfStep, newDefined, newGivens);
        pfStep = pfStep.nextSibling;
      }
      while (pfStep != null);
    }
  } else { // Gap
    if (newDefined != null) {
      addSetToSet(d.defined, newDefined);
    }
    if (newGivens != null) {
      var theGiven;
      var details = step.firstChild.lastChild;
      if (d.kind == noGoalGap) {
        for (theGiven of newGivens) {
          details.appendChild(makeGGPane(given, theGiven))
        }
      } else {
        var goalHead = details.lastChild.previousSibling;
        for (theGiven of newGivens) {
          details.insertBefore(makeGGPane(given, theGiven), goalHead);
        }
      }  
    }
  }
}

/* Add context of this step to nowDefined and nowKnown.  If nowDefined == null,
don't do nowDefined.
*/
function addContext(step, nowDefined, nowKnown) {
  var pf = step.parentNode;
  if (pf != mainProof) {
    pf = pf.parentNode;
    addContext(pf.parentNode, nowDefined, nowKnown);
  }
  var pfData = getData(pf);
  if ((pfData.defined != null) && (nowDefined != null)) {
    addSetToSet(nowDefined, pfData.defined);
  }
  if (pfData.premises != null) {
    addSetToSet(nowKnown, pfData.premises);
  }
  var nextStep = step.parentNode.firstChild;
  while (nextStep != step) {
    var stepData = getData(nextStep);
    if (stepData.kind == inference) {
      if ((stepData.defined != null) && (nowDefined != null)) {
        addSetToSet(nowDefined, stepData.defined);
      }
      if (stepData.inferred != null) {
        addSetToSet(nowKnown, stepData.inferred);
      }
    } else if (stepData.kind == goalGap) {
      var goalStmnt = getGoal(nextStep);
      if (goalStmnt != null) {
        addElemToSet(nowKnown, goalStmnt);
      }
    } else if (stepData.kind == defineGoalGap) {
      if (nowDefined != null) {
        addElemToSet(nowDefined, getDefineGoal(nextStep));
      }
    }
    nextStep = nextStep.nextSibling;
  }
}

/* Starting at step, remove delDefine from defined variables and delAssert from Givens
of all gaps.  If statements in delAssert get asserted, remove them -- no longer
need to be deleted.
*/
function deleteContext(step, delDefine, delAssert) {
  var i, c
  do {
    var stepData = getData(step);
    if (stepData.kind == inference) {
      if (stepData.subproofs != noSubproofs) {
        c = step.childNodes;
        var proofRange = getProofRange(step);
        for (i = proofRange.first; i <= proofRange.last; i++) {
          var subpf = c[i];
          var subpfData = getData(subpf);
          var delAssertCopy = (delAssert == null) ? null : delAssert.slice(0);
          if ((delAssertCopy != null) && (subpfData.premises != null)) {
            removeSetFromSet(delAssertCopy, subpfData.premises);
          }
          deleteContext(subpf.lastChild.firstChild, delDefine, delAssertCopy);
        }
      }
    } else {
      if (delDefine != null) {
        removeSetFromSet(stepData.defined, delDefine);
      }
      if (delAssert != null) {
        var details = step.firstChild.lastChild;
        var numGiven = numGivens(stepData.kind, details);
        for (i = numGiven; i >= 1; i--) {
          var given = details.childNodes[i];
          if (delAssert.includes(getData(given).theStmnt)) {
            details.removeChild(given);
          }
        }
        if (stepData.kind == goalGap) {
          var goalStmnt = getGoal(step);
          if (goalStmnt != null) {
            i = delAssert.indexOf(goalStmnt);
            if (i > -1) {
              delAssert.splice(i, 1);
            }
          }
        }
      }
    }
    step = step.nextSibling;
  } while (step != null);
}

/* Starting at step, find first step where a variable in delDefine or a statement in delAssert
is used.  Return null if never used.  Note:  delAssert may be changed, so if need original,
copy before calling firstUse.
*/
function firstUse(step, delDefine, delAssert) {
  var i, c, whereUsed, usedStmnt;
  do {
    var stepData = getData(step);
    if (stepData.kind == inference) {
      if (stepData.subproofs != noSubproofs) {
        c = step.childNodes;
        var proofRange = getProofRange(step);
        for (i = proofRange.first; i <= proofRange.last; i++) {
          var subpf = c[i];
          var subpfData = getData(subpf);
          var delAssertCopy = (delAssert == null) ? null : delAssert.slice(0);
          if (subpfData.premises != null) {
            if (usedInList(subpfData.premises, delDefine, delAssertCopy)) {
              return step;
            }
          }
          whereUsed = firstUse(subpf.lastChild.firstChild, delDefine, delAssertCopy);
          if (whereUsed != null) {
            return whereUsed;
          }
        }
      }
      if ((stepData.used != null) && (delAssert != null)) {
        for (usedStmnt of stepData.used) {
          if (delAssert.includes(usedStmnt)) {
            return step;
          }
        }
      }
      if (stepData.inferred != null) {
        if (usedInList(stepData.inferred, delDefine, delAssert)) {
          return step;
        }
      }
    } else if (stepData.kind == goalGap) {
      var theGoal = getGoal(step);
      if (theGoal != null) {
        if (usedInList([theGoal], delDefine, delAssert)) {
          return step;
        }
      }
    }
    step = step.nextSibling;
  } while (step != null);
  return null;
}

/* See if vars in delDefine are used in stmnts in the list.  If not, remove elements of list from
delAssert.  Use this in a proof part in which theList is a list of statements being asserted.
Either delDefine or delAssert may be null.
*/
function usedInList(theList, delDefine, delAssert) {
  var v, s;
  if (delDefine != null) {
    for (v of delDefine) {
      for (s of theList) {
        if (s[0].theForm.hasFree(v)) {
          return true;
        }
      }
    }
  }
  if (delAssert != null) {
    removeSetFromSet(delAssert, theList);
  }
  return false;
}

function willBeDefined(step, includeThis) {
  var result = [];
  if (!includeThis) {
    step = step.nextSibling;
  }
  while (step != null) {
    addDefinedTo(step, result);
    step = step.nextSibling;
  }
  return result;
}

function addDefinedTo(step, varSet) {
  var i, c, proofRange, subpf, subDefined, subStep;
  var d = getData(step);
  if (d.kind == defineGoalGap) {
    addElemToSet(varSet, getDefineGoal(step));
  } else if (d.kind == inference) {
    if (d.defined != null) {
      addSetToSet(varSet, d.defined);
    }
    if (d.subproofs != noSubproofs) {
      proofRange = getProofRange(step);
      c = step.childNodes;
      for (i = proofRange.first; i <= proofRange.last; i++) {
        subpf = c[i];
        subDefined = getData(subpf).defined;
        if (subDefined != null) {
          addSetToSet(varSet, subDefined);
        }
        subStep = subpf.lastChild.firstChild;
        do {
          addDefinedTo(subStep, varSet);
          subStep = subStep.nextSibling;
        } while (subStep != null);
      }
    }
  }
}

// Adjust show/hide buttons when gap added or removed from steps of a subproof:
function gapAdded(steps) {
  var pf;
  while (steps != mainProof) {
    pf = steps.parentNode;
    if (!pf.firstChild.classList.contains("complete")) {
      return;
    }
    pf.firstChild.classList.remove("complete");
    steps = pf.parentNode.parentNode;
  }
}

function gapRemoved(steps) {
  var pf, nextStep, i, d, c, proofRange;
  do {
    nextStep = steps.firstChild;
    do {
      d = getData(nextStep);
      if (d.kind != inference) {
        return;
      }
      if (d.subproofs != noSubproofs) {
        c = nextStep.childNodes;
        proofRange = getProofRange(nextStep);
        for (i = proofRange.first; i <= proofRange.last; i++) {
          if (!c[i].firstChild.classList.contains("complete")) {
            return;
          }
        }
      }
      nextStep = nextStep.nextSibling;
    } while (nextStep != null);
    if (steps == mainProof) {
       showMessage("Congratulations! You have completed the proof.");
       return;
    } else {
      var pf = steps.parentNode;
      pf.firstChild.classList.add("complete");
      steps = pf.parentNode.parentNode;
    }
  } while (true);
}

/* Try to match formula with element of list.  If no match, see if formula has kind listKind,
and if so, see if arguments of formula match elements of list.  Remove all matches, and
return true if formula or all arguments match.  listKind must be a MultiCompoundFormula kind.
*/
function cutFromList(form, list, listKind) {
	var i, j;
	var listSize = list.length;
	for (i = 0; i < listSize; i++) {
		if (formMatch(form, list[i], true)) {
			list.splice(i, 1);
			return true;
		}
	}
	if (form.kind != listKind) {
		return false;
	}
	var args = form.args;
	var numArgs = args.length;
	matchArguments: for (j = 0; j < numArgs; j++) {
		var theArg = args[j];
		for (i = 0; i < listSize; i++) {
			if (formMatch(theArg, list[i], true)) {
				list.splice(i, 1);
				listSize--;
				continue matchArguments;
			}
		}
		return false;
	}
	return true;
}

/* Add formula to list.  If it has kind listKind and no parens, add its arguments rather than
the formula itself.  listKind must be a MultiCompoundFormula kind.
*/
function addToList(form, list, listKind) {
	var i;
	if ((form.kind == listKind) && (form.parens == null)) {
		var arg;
		for (arg of form.args) {
			list.push(arg);
		}
	} else {
		list.push(form);
	}
}

function mergeList(theList, stmnt1, stmnt2, replacement) {
  var noneFound = true;
  var n = theList.length;
  var i = 0;
  while (i < n) {
    if ((theList[i] == stmnt1) || (theList[i] == stmnt2)) {
      if (noneFound) {
        theList[i] = replacement;
        noneFound = false;
        i++;
      } else {
        theList.splice(i, 1);
        n--;
      }
    } else {
      i++;
    }
  }
}

function merge(data, steps, givenStmnt, goalStmnt, merged) {
  var i, c, details, foundGiven, gg, ggData;
  if (data.premises != null) {
    mergeList(data.premises, givenStmnt, goalStmnt, merged);
  }
  var nextStep = steps.firstChild;
  while (nextStep != null) {
    var stepData = getData(nextStep);
    if (stepData.kind == inference) {
      if (stepData.used != null) {
        mergeList(stepData.used, givenStmnt, goalStmnt, merged);
      }
      if (stepData.inferred != null) {
        mergeList(stepData.inferred, givenStmnt, goalStmnt, merged);
      }
      if (stepData.subproofs != noSubproofs) {
        var proofRange = getProofRange(nextStep);
        c = nextStep.childNodes;
        for (i = proofRange.first; i <= proofRange.last; i++) {
          var subpf = c[i];
          merge(getData(subpf), subpf.lastChild, givenStmnt, goalStmnt, merged);
        }
      }
    } else {
      details = nextStep.firstChild.lastChild;
      var lastGiven = numGivens(stepData.kind, details);
      foundGiven = false;
      i = 1
      while (i <= lastGiven) {
        gg = details.childNodes[i];
        ggData = getData(gg);
        if ((ggData.theStmnt == givenStmnt) || (ggData.theStmnt == goalStmnt)) {
          if (foundGiven) {
            details.removeChild(gg);
            lastGiven--;
          } else {
            details.replaceChild(makeGGPane(ggData.kind, merged), gg);
            foundGiven = true;
            i++;
          }
        } else {
          i++;
        }
      }
      if (stepData.kind == goalGap) {
        gg = details.lastChild;
        ggData = getData(gg);
        if ((ggData.theStmnt == givenStmnt) || (ggData.theStmnt == goalStmnt)) {
          details.replaceChild(makeGGPane(ggData.kind, merged), gg);
        }
      }
    }
    nextStep = nextStep.nextSibling;
  }
}

function addElemToSet(theSet, elemToAdd) {
  if (!theSet.includes(elemToAdd)) {
    theSet.push(elemToAdd);
  }
}

function addSetToSet(theSet, toAdd) {
  var v;
  for (v of toAdd) {
    if (!theSet.includes(v)) {
      theSet.push(v);
    }
  }
}

function removeSetFromSet(theSet, toRemove) {
  var v, pos;
  for (v of toRemove) {
    pos = theSet.indexOf(v);
    if (pos > -1) {
      theSet.splice(pos, 1);
    }
  }
}

function getNewVar(field, haveDefined, willDefine, doAfter = null) {
	var theVar = parseVar(field);
	if (theVar == null) {
		showMessage("Illegal variable name.", doAfter);
		return null;
	}
	if (haveDefined.includes(theVar)) {
		alreadyDefinedError(theVar, doAfter);
		return null;
	}
	if ((willDefine != null) && willDefine.includes(theVar)) {
		willDefineError(theVar, doAfter);
		return null;
	}
	return theVar;
}

function checkDefined(definedVars, form, doAfter = null) {
  var formVars = [];
	form.addVars(formVars, true);
  var i;
  var n = formVars.length;
  for (i = 0; i < n; i++) {
    if (!definedVars.includes(formVars[i])) {
      showMessage("What's " + textToElemHTML(varToText(formVars[i]), "span", false) +
        "? You can't use a variable until it has been defined", doAfter);
      return false;
    }
  }
  return true;
}

function makeRadioGroup(label, setButtons, includeField) {
  function buttonChange(btn, withField) {
    if (btn.checked) {
      if (withField) {
        btn.parentNode.parentNode.lastChild.focus();
      } else {
        window.getSelection().empty();
      }
      setButtons();
    }
  }

  function fieldGotFocus(field) {
    field.parentNode.firstChild.firstChild.checked = true;
    fieldFocus(field);
    setButtons();
  }

  var result = document.createElement("DIV");
  var button = document.createElement("INPUT");
  button.type = "radio";
  button.name = "group";
  if (includeField) {
    button.onchange = function() {buttonChange(this, true)};
  } else {
    button.onchange = function() {buttonChange(this, false)};
  }
  var labelSpan = document.createElement("SPAN");
  labelSpan.innerHTML = label;
  labelSpan.style.marginLeft = radioCheckSpace + "em";
  var radioPanel = document.createElement("LABEL");
  radioPanel.appendChild(button);
  radioPanel.appendChild(labelSpan);
  result.appendChild(radioPanel);
  if (includeField) {
    var field = makeMathField();
    field.style.marginBottom = "0.66em";
    field.style.marginLeft = "1.25em";
    field.oninput = setButtons;
    field.onfocus = function() {fieldGotFocus(this)};
    result.appendChild(field);
  }
  return result;
}
