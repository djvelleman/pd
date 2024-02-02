// Strategy menu commands
"use strict";

function doContrad() {
  var goalStatement, numSelected;
  var toContradict, theContrad;
  helpURL = "help/Contrad.html";
  commandName = "Contradiction";
  if (!gapSelected(true)) {
    useError();
    return;
  }
  goalStatement = getGoal(selectedStep);
  numSelected = selection.length;
  theContrad = null;
  var i = 0;
  while (i < numSelected) {
    var ggData = getData(selection[i].parentNode);
    i++;
    if (ggData.kind == given) {
      if (i < numSelected) {
        useError();
        return;
      }
      toContradict = ggData.theStmnt;
      theContrad = negateStmnt(toContradict);
      break;
    }
  }
  if (goalStatement == null) {
    if (theContrad == null) {
      useError();
      return;
    }
    backwardStep(selectedStep, null, [theContrad], [toContradict, theContrad], null);
  } else {
    var theGap = selectedStep;
    prepareStep();
    var theInference = inferenceBySubproof(theGap, null, null,
        [negateStmnt(goalStatement)], null, null, null, true);
    if (theContrad != null) {
      var steps = theInference.firstChild.lastChild;
      var details = steps.firstChild.firstChild.lastChild;
      details.replaceChild(makeGGPane(goal, theContrad), details.lastChild);
      details.previousSibling.innerHTML = proofHereTextHTML(theContrad);
      steps.appendChild(makeInference(null, [toContradict, theContrad], null, null));
    }
    theGap.parentNode.replaceChild(theInference, theGap);
  }
}

function doCases() {
  var nextPrefix, caseStmntList, caseTextHTML, numSelected;
  var numCases, caseForms, usedStmnts, form, i, casePrefix;
  var definedVars, caseField, okButton, cancelButton;

  function setUpCase(caseNum) {
    nextPrefix = casePrefix + (caseNum + 1) + ".";
    var nextForm = caseForms[caseNum];
    var caseFWT = {theForm: nextForm, theText: nextForm.toText()};
    caseStmntList = [[caseFWT]];
    caseTextHTML = "Case " + nextPrefix + " " + textToElemHTML(caseFWT.theText, "span", true) + ".";
  }

  function finishCases() {
    var goalStmnt, theInference, theGap, infTextHTML, subpf, subpfData, infPane;
    theGap = selectedStep;
    prepareStep();
    casePrefix = getData(getProof(theGap)).casePrefix;
    goalStmnt = getGoal(theGap);
	  infTextHTML = "Since this exhausts all the possible cases, we can conclude that " +
		    ((goalStmnt == null) ? "we have reached a contradiction." :
		    (textToElemHTML(goalStmnt[0].theText, "span", true) + "."));
	  setUpCase(0);
	  theInference = inferenceBySubproof(theGap, usedStmnts, null, caseStmntList,
		    goalStmnt, infTextHTML, caseTextHTML, true);
	  subpf = theInference.firstChild;
    infPane = subpf.nextSibling;
    subpfData = getData(subpf);
	  subpfData.casePrefix = nextPrefix;
    var dotsHTML = subpf.childNodes[2].innerHTML;
    var lemmaDepth = subpfData.lemmaDepth;
	  for (i = 1; i < numCases; i++) {
	  	setUpCase(i);
	  	subpf = makeSubproofStruct(null, caseStmntList, nextPrefix, lemmaDepth,
	  		caseTextHTML, dotsHTML);
	  	theInference.insertBefore(subpf, infPane);
	  	subpf.lastChild.appendChild(updateGoalGap(theGap, null, caseStmntList, goalStmnt));
	  }
   theGap.parentNode.replaceChild(theInference, theGap);
  }

  function afterError() {
    caseField.focus();
    selectWholeField(caseField);
  }

  function doOK() {
    form = parse(caseField, bool);
    if (form == null) {
      return;
    }
    if (checkDefined(definedVars, form, afterError)) {
      hideDialog();
      caseForms = [form, negate(form.cloneForm())];
      numCases = 2;
      usedStmnts = null;
      finishCases();
    }
  }
  
  function setOKButton() {
    okButton.disabled = (caseField.childNodes.length == 0);
  }

  // Beginning of doCases
  helpURL = "help/Cases.html";
  commandName = "Cases";
  if (!gapSelected(true)) {
    useError();
    return;
  }
  numSelected = selection.length;
	if (numSelected > 1) {
		useError();
		return;
	}
	if (numSelected == 1) {
		var selectedPane = selection[0];
    var selectedData = getData(selectedPane.parentNode);
		if (selectedData.kind == given) {
			var disjStmnt = selectedData.theStmnt;
      form = disjStmnt[getData(selectedPane).variant].theForm;
			if (form.kind != disj) {
				useError();
				return;
			}
			usedStmnts = [disjStmnt];
			var cases = form.args;
			numCases = cases.length;
			caseForms = [];
			for (i = 0; i < numCases; i++) {
				form = cases[i].cloneForm();
				form.parens = null;
				caseForms.push(form);
			}
      finishCases();
      return;
		}
	}
  definedVars = getData(selectedStep).defined;
  var casesDialog = makeDialog(42);
  casesDialog.style.textAlign = "center";
  casesDialog.appendChild(mathPal);
  var headPane = makeTextPane("Choose cases:<br>" + spacerHTML(0.66) + "Case 1. " + textToElemHTML("P", "span", false) +
      "<br>" + spacerHTML(0.66) + "Case 2. " + textToElemHTML(symbols[neg].letter + "P", "span", false), 1.25, 0);
  headPane.style.display = "inline-block";
  headPane.style.textAlign = "left";
  casesDialog.appendChild(headPane);
  var d = document.createElement("DIV");
  d.className = "tableGrid";
  d.style.gridTemplateColumns = "max-content auto";
  d.style.justifyContent = "stretch";
  d.style.margin = "1.25em 0em";
  var entryLabel = document.createElement("DIV");
  entryLabel.innerHTML = textToElemHTML("P", "span", false) + " =";
  entryLabel.style.marginRight = "0.66em";
  d.appendChild(entryLabel);
  caseField = makeMathField();
  caseField.style.textAlign = "left";
  d.appendChild(caseField);
  casesDialog.appendChild(d);
  var okCancelPanel = makeButtonPanel(["OK", "Cancel"]);
  okButton = okCancelPanel.firstChild;
  cancelButton = okButton.nextSibling;
  okButton.onclick = doOK;
  cancelButton.onclick = function() {hideDialog()};
  caseField.oninput = setOKButton;
  casesDialog.appendChild(okCancelPanel);
  showDialog(casesDialog, okButton, true);
  caseField.focus();
  setOKButton();
}

function doReexSub(reex) {
  var gapData, paneKind, theStmnt, mainFormText, avoidVars, theDialog, selectField, changeMade;
  var minorEdits, renameVar, addParens, addBrackets, removeGrouping;
  var majorEdits, negative, applyDef, subMenuCont, subButton, subMenu;
  var i, j, n, c, lastGiven, subList, usedStmnts, subMenuHTML, subMenuItem, details;
  var givenStmnt, givenFWT, givenForm, givenText, leftHTML, rightHTML;
  var okCancelPanel, okButton, cancelButton, selLeft, selRight, focusFunction;

  function doRenameVar(e) {
    var qfiedForm, defVars, varDialog, varField, dlogOKCancel, dlogOK, dlogCancel;

    function afterError() {
      varField.focus();
      selectWholeField(varField);
    }

    function finishRenameVar() {
      var newVar = parseVar(varField);
      if (newVar == null) {
        showMessage("Illegal variable name.", afterError);
        return;
      }
      if (defVars.includes(newVar)) {
        showMessage("You can't rename the bound variable " +
          textToElemHTML(varToText(newVar), "span", false) +
          ", because it would conflict with another variable.", afterError);
        return;
      }
	    addElemToSet(avoidVars, newVar);
		  qfiedForm.scope = qfiedForm.scope.plugIn(qfiedForm.bdVar, newVar, avoidVars, true);
      qfiedForm.bdVar = newVar;
      hideDialog();
      finishChange();
      selectSubform();
    }

    function fixOK() {
      dlogOK.disabled = (varField.childNodes.length == 0);
    }
  
    e.stopPropagation(); // So windowClick won't be called.
    qfiedForm = subformSpec.subForm;
		defVars = [];
    qfiedForm.addVars(defVars, true);
    varDialog = makeDialog(20);
    varDialog.style.textAlign = "center";
    varDialog.appendChild(makeTextPane("Choose a new name for the bound variable:", 0, 0));
    varField = makeMathField();
    varField.style.width = varFieldWidth + "em";
    varField.style.margin = "1.25em auto 1.25em";
    varField.style.textAlign = "left";
    varDialog.appendChild(varField);
    dlogOKCancel = makeButtonPanel(["OK", "Cancel"]);
    dlogOK = dlogOKCancel.firstChild;
    dlogCancel = dlogOKCancel.lastChild;
    dlogOK.onclick = finishRenameVar;
    dlogOK.disabled = true;
    dlogCancel.onclick = function() {hideDialog(selectSubform)};
    varDialog.appendChild(dlogOKCancel);
    varField.oninput = fixOK;
    showDialog(varDialog, dlogOK, true);
    varField.focus();
  }

  function doAddGrouping(groupChar, doFinish) {
    if (subformSpec.subEnd == 0) {
      subformSpec.subForm.parens = groupChar;
    } else {
      var parent = subformSpec.parentForm;
      var newForm = new MultiCompoundFormula(parent.kind, parent.objType,
          parent.args.slice(subformSpec.subLoc, subformSpec.subEnd + 1));
      newForm.parens = groupChar;
      installSubform(newForm);
    }
    if (doFinish) {
      finishChange();
    }
  }

  function doRemoveGrouping() {
    subformSpec.subForm.parens = null;
    installSubform(subformSpec.subForm);
    finishChange();
  }

  function doReexNeg() {
		var unNegatedForm = subformSpec.subForm.right;
		unNegatedForm.parens = null;
		var unNegKind = unNegatedForm.kind;
		var qfied = ((unNegKind == all) || (unNegKind == exist));
		installSubform(unNegatedForm.smartNegate(avoidVars));
		if (qfied) {
			subformSpec.parentForm = unNegatedForm;
			subformSpec.subLoc = locScope;
			subformSpec.subForm = unNegatedForm.scope;
		}
    finishChange();
  }

  function doMakeNeg() {
		if (subformSpec.subEnd != 0) {
			doAddGrouping('(', false);
		}
		var subKind = subformSpec.subForm.kind;
		var qfied = ((subKind == all) || (subKind == exist));
		var negSubForm = subformSpec.subForm.smartNegate(avoidVars);
		var equivSubForm = new CompoundFormula(neg, bool, null, negSubForm);
		installSubform(equivSubForm);
		if (qfied) {
			subformSpec.parentForm = negSubForm;
			subformSpec.subLoc = locScope;
			subformSpec.subForm = negSubForm.scope;
		} else {
			subformSpec.parentForm = equivSubForm;
			subformSpec.subLoc = locRight;
			subformSpec.subForm = negSubForm;
		}
    finishChange();
  }

  function doApplyDef() {
    var oldParens = subformSpec.subForm.parens;
		var newForm = subformSpec.subForm.define(avoidVars);
		if ((newForm.kind < all) && (newForm.kind != neg)) {
			newForm.parens = oldParens;
    }
    installSubform(newForm);
    finishChange();
  }

  function doSub(whichSub) {
    var theSub = subList[whichSub];
    var toReplaceVars = [];
    theSub.toReplace.addVars(toReplaceVars, true);
    var replacementVars = [];
    theSub.replacement.addVars(replacementVars, true);
    var i, v;
    for (v of subformSpec.boundVars) {
      if (toReplaceVars.includes(v)) {
        return;
      }
      i = replacementVars.indexOf(v);
      if (i >= 0) {
        replacementVars[i] = -v - 1;
      }
    }
    repInfo = {toReplace: theSub.toReplace, replacement: theSub.replacement,
      toReplaceVars: toReplaceVars, replacementVars: replacementVars, boundSubs: [], didSub: false};
    if (subformSpec.subEnd == 0) {
      installSubform(subformSpec.subForm.subForTerm());
    } else {
      var parent = subformSpec.parentForm;
      var oldSize = parent.args.length;
      parent.subForTermRange(subformSpec.subLoc, subformSpec.subEnd);
      subformSpec.subForm = parent.args[subformSpec.subLoc];
      subformSpec.subEnd += parent.args.length - oldSize;
      if (subformSpec.subEnd == subformSpec.subLoc) {
        subformSpec.subEnd = 0;
      }
    }
    if (!repInfo.didSub) {
      return;
    }
    var boundSubs = repInfo.boundSubs;
    var boundReps = [];
    var n = boundSubs.length;
		v = -1;
		for (i = 0; i < n; i++) {
			v = findNextVar(avoidVars, true, v);
			boundReps.push(v);
		}
		subformSpec.mainForm.subBoundVars(boundSubs, boundReps);
    addElemToSet(usedStmnts, theSub.eqnStmnt);
    finishChange();
  }

  function showSubMenu(e) {
    if (subMenu.classList.contains("hide")) {
      selectField.tabIndex = -1;
      selectField.classList.add("unselectable");
      selectField.onfocus = function() {selectField.blur()};
      setSelEnds();
      selectField.blur();
      updateSelection(selectField, selLeft, selRight);
      subMenu.classList.remove("hide");
      var allButtons = theDialog.getElementsByTagName("BUTTON");
      var b;
      for (b of allButtons) {
        b.disabled = true;
        b.style.pointerEvents = "none";
      }
      e.stopPropagation();
    }
  }

  function windowClick() {
    if (!reex && !subMenu.classList.contains("hide")) {
      selectField.tabIndex = 0;
      selectField.classList.remove("unselectable");
      selectField.onfocus = focusFunction;
      subMenu.classList.add("hide");
      var allButtons = theDialog.getElementsByTagName("BUTTON");
      var b;
      for (b of allButtons) {
        b.style.pointerEvents = "auto";
      }
    }
    selectSubform();
  }

  function setSelEnds() {
    selLeft = subformSpec.subForm.first;
    if (subformSpec.subEnd > 0) {
      selRight = subformSpec.parentForm.args[subformSpec.subEnd].last + 1;
    } else {
      selRight = subformSpec.subForm.last + 1;
    }
  }

  function selectSubform() {
    setSelEnds();
    selectField.focus();
    updateSelection(selectField, selLeft, selRight);
    setButtons();
  }

  function installSubform(newForm) {
    subformSpec.subForm = newForm;
    if (subformSpec.parentForm == null) {
      subformSpec.mainForm = newForm;
    } else {
      subformSpec.parentForm.changeSubform()
    }
  }

  function finishChange() {
    mainFormText = subformSpec.mainForm.toText();
    selectField.innerHTML = textToHTML(mainFormText, false);
    changeMade = true;
  }

  function finishReexSub(e) {
    var newFWT = {theForm: subformSpec.mainForm, theText: mainFormText};
    finishReexSubDialog(e);
    if (usedStmnts.length == 0) {
      addVariant(theStmnt, newFWT);
    } else {
      var newStmnt = [newFWT];
      if (paneKind == given) {
        addElemToSet(usedStmnts, theStmnt);
        forwardStep(selectedStep, null, usedStmnts, null, [newStmnt], null, false);
      } else {
        addElemToSet(usedStmnts, newStmnt);
        backwardStep(selectedStep, null, [newStmnt], usedStmnts, null);
      }
    }
  }

  function finishReexSubDialog(e) {
    e.stopPropagation();  // So windowClick won't be called
    subformSpec = null;  //For garbage collection
    repInfo = null;
    hideDialog();
  }

  function setButtons() {
    var noRange = (subformSpec.subEnd == 0);
    var selectedKind = subformSpec.subForm.kind;
    renameVar.disabled = (!noRange || (selectedKind < all) || (selectedKind > unique));
    addParens.disabled = false;
    addBrackets.disabled = (noRange && (selectedKind == pair));
    if ((subformSpec.subForm.parens == null) || !noRange || (selectedKind == pair)) {
      removeGrouping.disabled = true;
    } else {
      var parent = subformSpec.parentForm;
      if (parent == null) {
        removeGrouping.disabled = false;
      } else {
        removeGrouping.disabled = !parent.subCanRemoveGrouping();
      }
    }
    if (reex) {
      if (noRange && (selectedKind == neg)) {
        negative.textContent = "Reexpress Negative";
        negative.onclick = doReexNeg;
      } else {
        negative.textContent = "Make Negative";
        negative.onclick = doMakeNeg;
      }
      negative.disabled = (subformSpec.subForm.objType != bool);
      applyDef.disabled = !(noRange && subformSpec.subForm.isDefinable());
    } else {
      subButton.disabled = false;
    }
    okButton.disabled = !changeMade;
    cancelButton.disabled = false;
  }

  function subformAdjustMySel() {
    subformSpec.boundVars = [];
    subformSpec.subEnd = 0;
    if (subformSpec.mainForm.searchSubform()) {
      subformSpec.parentForm = null;
      subformSpec.subForm = subformSpec.mainForm;
    }
    mySel.start = subformSpec.subForm.first;
    if (subformSpec.subEnd > 0) {
      mySel.end = subformSpec.parentForm.args[subformSpec.subEnd].last + 1;
    } else {
      mySel.end = subformSpec.subForm.last + 1;
    }
    setButtons();
  }

  function truncFormHTML(text, form) {
    var textPart = text.slice(form.first, form.last + 1);
    if (textPart.length > maxSubMenuChars) {
      return textToHTML(textPart.slice(0, maxSubMenuChars)) + "\u2026";
    }
    return textToHTML(textPart);
  }

  // Beginning of doReexSub
  if (reex) {
    helpURL = "help/Reexpress.html";
    commandName = "Reexpress";
  } else {
    helpURL = "help/Substitute.html";
    commandName = "Substitute";
  }
  if (selection.length != 1) {
    useError();
    return;
  }
  var selectedPane = selection[0];
  paneKind = getVarKind(selectedPane);
	if (paneKind == defineGoal) {
		useError();
		return;
	}
	theStmnt = getData(selectedPane.parentNode).theStmnt;
	if (theStmnt == null) {
		useError();
		return;
	}
  var oldVariant = theStmnt[getData(selectedPane).variant];
  var mainForm = oldVariant.theForm.cloneForm();
  mainFormText = oldVariant.theText;
  subformSpec = {mainForm: mainForm, parentForm: null, subForm: mainForm, subLoc: 0, subEnd: 0, boundVars: []};
  gapData = getData(selectedStep);
  avoidVars = willBeDefined(selectedStep, true);
  addSetToSet(avoidVars, gapData.defined);
  subformSpec.mainForm.addVars(avoidVars, false);
  changeMade = false;
  usedStmnts = [];
  theDialog = makeDialog(42);
  selectField = makeMathField();
  selectField.innerHTML = textToHTML(mainFormText, false);
  selectField.contentEditable = false;
  selectField.onkeydown = null;
  selectField.onblur = null;
  focusFunction = selectField.onfocus;
  theDialog.appendChild(selectField);
  getData(selectField).adjustMySel = subformAdjustMySel;
  minorEdits = makeButtonPanel(["Rename Bound Variable", "( . . . )", "[ . . . ]", "Remove ( ) or [ ]"]);
  renameVar = minorEdits.firstChild;
  renameVar.onclick = function(event) {doRenameVar(event)};
  addParens = renameVar.nextSibling;
  addParens.onclick = function() {doAddGrouping("(", true);};
  addBrackets = addParens.nextSibling;
  addBrackets.onclick = function() {doAddGrouping("[", true);};
  removeGrouping = addBrackets.nextSibling;
  removeGrouping.onclick = doRemoveGrouping;
  minorEdits.style.padding = "1.25em 0em 0.66em";
  theDialog.appendChild(minorEdits);
  majorEdits;
  if (reex) {
    majorEdits = makeButtonPanel(["Reexpress Negative", "Apply Definition"]);
    negative = majorEdits.firstChild;
    applyDef = majorEdits.lastChild;
    applyDef.onclick = doApplyDef;
  } else {
    majorEdits = document.createElement("DIV");
    majorEdits.style.textAlign = "center";
    majorEdits.innerHTML = "<div class='menu-container'><div style='padding: 0.1em 0.25em; border: 1px solid gray'>Substitute</div><div class='menu-background hide' style='text-align: left'></div></div>";
    subMenuCont = majorEdits.firstChild;
    subButton = subMenuCont.firstChild;
    subMenu = subMenuCont.lastChild;
    subList = [];
    subMenuHTML = "";
    details = selectedStep.firstChild.lastChild;
    lastGiven = numGivens(gapData.kind, details);
    c = details.childNodes;
    for (i = 1; i <= lastGiven; i++) {
      givenStmnt = getData(c[i]).theStmnt;
      n = givenStmnt.length;
      for (j = 0; j < n; j++) {
        givenFWT = givenStmnt[j];
        givenForm = givenFWT.theForm;
        if (givenForm.kind == equals) {
          givenText = givenFWT.theText;
          leftHTML = truncFormHTML(givenText, givenForm.left);
          rightHTML = truncFormHTML(givenText, givenForm.right);
          subMenuHTML += "<div class='menu-item submenu-item' id='" +
            subList.length + "'>" + leftHTML + " \u21D2 " + rightHTML + "</div>";
          subList.push({eqnStmnt: givenStmnt, toReplace: givenForm.left, replacement: givenForm.right});
          subMenuHTML += "<div class='menu-item submenu-item' id='" +
            subList.length + "'>" + rightHTML + " \u21D2 " + leftHTML + "</div>";
          subList.push({eqnStmnt: givenStmnt, toReplace: givenForm.right, replacement: givenForm.left});
        }
      }
    }
    if (subList.length == 0) {
      subButton.textContent = "No Substitutions Available";
    } else {
      subMenu.innerHTML = subMenuHTML;
      for (subMenuItem of subMenu.childNodes) {
        subMenuItem.onclick = function() {doSub(parseInt(this.id))};
      }
      subButton.onclick = function(event) {showSubMenu(event)};
    }
  }
  majorEdits.style.paddingBottom = "0.66em";
  theDialog.appendChild(majorEdits);
  okCancelPanel = makeButtonPanel(["OK", "Cancel"]);
  okButton = okCancelPanel.firstChild;
  okButton.onclick = function(event) {finishReexSub(event)};
  cancelButton = okCancelPanel.lastChild;
  cancelButton.onclick = function(event) {finishReexSubDialog(event)};
  theDialog.appendChild(okCancelPanel);
  showDialog(theDialog, okButton, true);
  theDialog.parentNode.onclick = windowClick;
  if (!reex) {
    subMenu.style.top = subButton.offsetHeight + "px";
  }
  selectSubform();
}

function doDefine() {
  var variableField, valueField, okButton, gapData, defaultVar, willDefine, errorField;

  function afterError() {
    errorField.focus();
  }

  function finishDefine() {
    errorField = variableField;
    var theVar = getNewVar(variableField, gapData.defined, willDefine, afterError);
    if (theVar == null) {
      return;
    }
    var theTerm = parse(valueField, set);
    if (theTerm == null) {
      return;
    }
    errorField = valueField;	
		if (!checkDefined(gapData.defined, theTerm, afterError)) {
			return;
		}
    hideDialog();
    var theGap = selectedStep;
    prepareStep();
    var theForm = new CompoundFormula(equals, bool, new AtomicTerm(theVar), theTerm);
    var infStmnt = makeStmnt(theForm);
    var infTextHTML = "Let " + textToElemHTML(infStmnt[0].theText, "span", true) + ".";
    forwardStep(theGap, null, null, [theVar], [infStmnt], infTextHTML, (theVar == defaultVar));
  }

  function setOKButton() {
    okButton.disabled = ((variableField.childNodes.length == 0) || (valueField.childNodes.length == 0));
  }

  helpURL = "help/Define.html";
  commandName = "Define";
  if (!gapSelected(false)) {
    useError();
    return;
  }
  gapData = getData(selectedStep);
  defaultVar = (gapData.kind == defineGoalGap) ? getDefineGoal(selectedStep) : null;
  willDefine = willBeDefined(selectedStep, false);

  var theDialog = makeDialog(42);
  theDialog.appendChild(mathPal);
  variableField = makeMathField();
  valueField = makeMathField();
  variableField.style.display = "inline-block";
  variableField.style.width = varFieldWidth + "em";
  variableField.style.margin = "0.66em 0.66em 0.66em";
  variableField.oninput = setOKButton;
  valueField.oninput = setOKButton;
  var letBox = document.createElement("DIV");
  letBox.style.display = "flex";
  letBox.style.alignItems = "center";
  letBox.appendChild(document.createTextNode("Let"));
  letBox.appendChild(variableField);
  letBox.appendChild(document.createTextNode("="));
  theDialog.appendChild(letBox);
  theDialog.appendChild(valueField);
  var okCancelPanel = makeButtonPanel(["OK", "Cancel"]);
  okCancelPanel.style.marginTop = "1.25em";
  theDialog.appendChild(okCancelPanel);
  okButton = okCancelPanel.firstChild;
  var cancelButton = okButton.nextSibling;
  okButton.onclick = finishDefine;
  cancelButton.onclick = function() {hideDialog()};
  showDialog(theDialog, okButton, true);
  if (defaultVar != null) {
    variableField.innerHTML = textToHTML(varToText(defaultVar));
    valueField.focus();
  } else {
    variableField.focus();
  }
  setOKButton();
}
