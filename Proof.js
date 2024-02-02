// Functions for creating and manipulating proofs
"use strict";

function makeProof(defined, premises, casePrefix, lemmaDepth) {
  var p = document.createElement("DIV");
  var d = makeData(p);
  d.defined = defined;
  d.premises = premises;
  d.casePrefix = casePrefix;
  d.lemmaDepth = lemmaDepth;
  return p;
}

function copyProof() { // Assume nothing is selected
  stmntCopyTable = [];
  var d = getData(mainProof);
  var copy = makeProof(d.defined.slice(0), copyStmntList(d.premises), d.casePrefix, d.lemmaDepth);
  copySteps(mainProof, copy);
  stmntCopyTable = null;
  return copy;
}

function copySteps(oldSteps, newSteps) {
  var c = oldSteps.childNodes;
  var n = c.length;
  var i, step;
  for (i = 0; i < n; i++) {
    step = c[i];
    if (getData(step).kind == inference) {
      newSteps.appendChild(copyInference(step));
    } else {
      newSteps.appendChild(copyGap(step));
    }
  }
}

// NOTE:  makeSupProof does not put anything in stepsPane.  defined and premises can  be null if none.
// conclusion can be null if contradiction.  introHTML cannot be null.
// Conclusion used only to construct innerHTML for dotsPane.
function makeSubproof(defined, premises, conclusion, casePrefix, lemmaDepth, introHTML) {
  return makeSubproofStruct(defined, premises, casePrefix, lemmaDepth, introHTML,
    makeDotsHTML(conclusion));
}

function makeDotsHTML(conclusion) {
  return spacerHTML(dotsIndent) + "\u22EE <br>" + thereforeTextHTML(conclusion);
}

function makeSubproofStruct(defined, premises, casePrefix, lemmaDepth, introHTML, dotsHTML) {
  var p = makeProof(defined, premises, casePrefix, lemmaDepth);
  p.className = "frame";
  var showHideButton = document.createElement("BUTTON");
  showHideButton.className = "show-hide";
  showHideButton.textContent = "\u2234";
  p.appendChild(showHideButton);
  var introPane = document.createElement("DIV");
  introPane.className = "intro";
  introPane.innerHTML = introHTML;
  p.appendChild(introPane);
  var dotsPane = document.createElement("DIV");
  dotsPane.className = "pad-left hide";  // Initially hidden
  dotsPane.innerHTML = dotsHTML;
  p.appendChild(dotsPane);
  var stepsPane = document.createElement("DIV");
  p.appendChild(stepsPane);
  showHideButton.onclick = function(event) {toggleSteps(event, p)};
  return p;
}

function copySubproof(p) {
  var d = getData(p);
  var copy = makeSubproofStruct((d.defined == null) ? null : d.defined.slice(0), (d.premises == null) ? null : copyStmntList(d.premises),
    d.casePrefix, d.lemmaDepth, p.childNodes[1].innerHTML, p.childNodes[2].innerHTML);
  if (p.firstChild.classList.contains("complete")) {
    copy.firstChild.classList.add("complete");
  }
  var stepsPane = p.lastChild;
  var copyStepsPane = copy.lastChild;
  copySteps(stepsPane, copyStepsPane);
  if (stepsPane.classList.contains("hide")) {
    copyStepsPane.classList.add("hide");
    copyStepsPane.previousSibling.classList.remove("hide");
  }
  return copy;
}

// defined and used can be null if none.  inferred is null if contradiction.  infHTML can be null: use default text.
function makeInference(defined, used, inferred, infHTML) {
  var inf = document.createElement("DIV");
  var d = makeData(inf);
  d.kind = inference;
  d.defined = defined;
  d.used = used;
  d.inferred = inferred;
  d.subproofs = noSubproofs; // Change if want to add subproofs
  var infPane = document.createElement("DIV");
  infPane.className = "pad-top pad-left";
  if (infHTML == null) {
    infHTML = sinceTextHTML(used, inferred);
  }
  infPane.innerHTML = infHTML;
  inf.appendChild(infPane);
  inf.onclick = function(event) {toggleStepSelected(event, this)};
  return inf;
}

function copyInference(inf) {
  var d = getData(inf);
  var infPane;
  if (d.subproofs == subproofsFirst) {
    infPane = inf.lastChild;
  } else {
    infPane = inf.firstChild;
  }
  var copy = makeInference((d.defined == null) ? null : d.defined.slice(0), (d.used == null) ? null : copyStmntList(d.used),
    (d.inferred == null) ? null : copyStmntList(d.inferred), infPane.innerHTML);
  if (d.subproofs == noSubproofs) {
    return copy;
  }
  getData(copy).subproofs = d.subproofs;
  var c = inf.childNodes;
  var i, last;
  if (d.subproofs == subproofsFirst) {
    var copyInfPane = copy.firstChild;
    last = c.length - 2;
    for (i = 0; i <= last; i++) {
      copy.insertBefore(copySubproof(c[i]), copyInfPane);
    }
  } else {
    last = c.length - 1;
    for (i = 1; i <= last; i++) {
      copy.appendChild(copySubproof(c[i]));
    }
  }
  return copy;
}

// defined, premises will not be null.  conclusion null for contradiction.
function makeGoalGap(defined, premises, conclusion) {
  var g = makeGapStruct(goalGap, defined, proofHereTextHTML(conclusion));
  var detailsPane = g.firstChild.lastChild;
  addGivens(detailsPane, premises);
  addGoal(detailsPane, conclusion);
  return g;
}

function makeNoGoalGap(defined, premises) {
  var g = makeGapStruct(noGoalGap, defined, "Additional steps go here.");
  addGivens(g.firstChild.lastChild, premises);
  return g;
}

function makeDefineGoalGap(defined, premises, toDef) {
var g = makeGapStruct(defineGoalGap, defined, definitionHereTextHTML(toDef));
var detailsPane = g.firstChild.lastChild;
addGivens(detailsPane, premises);
addDefineGoal(detailsPane, toDef);
return g;
}

function copyGap(gap) {
  var d = getData(gap);
  var detailsPane = gap.firstChild.lastChild;
  var copy = makeGapStruct(d.kind, d.defined.slice(0), detailsPane.previousSibling.innerHTML);
  var copyDetails = copy.firstChild.lastChild;
  if (detailsPane.classList.contains("hide")) {
    copyDetails.classList.add("hide");
  }
  copyGivens(d.kind, detailsPane, copyDetails, true);
  if (d.kind == noGoalGap) {
    return copy;
  }
  copyDetails.appendChild(makeHeading("Goal:"));
  if (d.kind == goalGap) {
    copyDetails.appendChild(copyGGPane(detailsPane.lastChild, true))
  } else {
    copyDetails.appendChild(makeDefineGoalPane(getData(detailsPane.lastChild).toDef));
  }
  return copy;
}

function copyGivens(kind, oldDetails, newDetails, copyTheStmnt) {
  var c = oldDetails.childNodes;
  var i;
  var lastGiven = numGivens(kind, oldDetails);
  for (i = 1; i <= lastGiven; i++) {
    newDetails.appendChild(copyGGPane(c[i], copyTheStmnt));
  }
}

function makeGapStruct(kind, defined, introHTML) {
  var g = document.createElement("DIV");
  var d = makeData(g);
  d.kind = kind;
  d.defined = defined;
  var frame = document.createElement("DIV");
  frame.className = "frame pink";
  g.appendChild(frame);
  var showHideButton = document.createElement("BUTTON");
  showHideButton.className = "show-hide";
  showHideButton.textContent = "?";
  frame.appendChild(showHideButton);
  var introPane = document.createElement("DIV");
  introPane.className = "intro";
  introPane.innerHTML = introHTML;
  frame.appendChild(introPane);
  var detailsPane = document.createElement("DIV");
  detailsPane.appendChild(makeHeading("Givens:"));
  frame.appendChild(detailsPane);
  showHideButton.onclick = function(event) {toggleDetails(event, g)};
  g.onclick = function(event) {toggleStepSelected(event, this)};
  return g;
}

function addGivens(details, premises) {
  var i;
  var l = premises.length;
  for (i = 0; i < l; i++) {
    details.appendChild(makeGGPane(given, premises[i]));
  }
}

function addGoal(details, conclusion) {
  details.appendChild(makeHeading("Goal:"));
  details.appendChild(makeGGPane(goal, conclusion));
}

function addDefineGoal(details, toDef) {
  details.appendChild(makeHeading("Goal:"));
  details.appendChild(makeDefineGoalPane(toDef));
}

// Given or goal pane.  statement == null for contradiction
function makeGGPane(kind, statement) {
  var p = document.createElement("DIV");
  var d = makeData(p);
  var i, l;
  d.kind = kind;
  d.theStmnt = statement;
  if (statement == null) {
    p.appendChild(makeVariantPane("<div>contradiction</div>", contrad));
  } else {
    l = statement.length;
    for (i = 0; i < l; i++) {
      p.appendChild(makeVariantPane(textToElemHTML(statement[i].theText, "div", true), i));
    }
  }
  if (kind == given) {
    setUpDrag(p);
  }
  return p;
}

function copyGGPane(pane, copyTheStmnt) {
  var oldData = getData(pane);
  var copy = document.createElement("DIV");
  var newData = makeData(copy);
  newData.kind = oldData.kind;
  if (oldData.theStmnt == null) {
    newData.theStmnt = null;
    copy.appendChild(makeVariantPane("<div>contradiction</div>", contrad));
  } else {
    if (copyTheStmnt) {
      newData.theStmnt = copyStmnt(oldData.theStmnt);
    } else {
      newData.theStmnt = oldData.theStmnt;
    }
    var i;
    var c = pane.childNodes;
    var n = c.length;
    for (i = 0; i < n; i++) {
      var variantNum = getData(c[i]).variant;
      copy.appendChild(makeVariantPane(textToElemHTML(newData.theStmnt[variantNum].theText, "div", true), variantNum));
    }
  }
  if (newData.kind == given) {
    setUpDrag(copy);
  }
  return copy;
}

function setUpDrag(pane) {
  pane.draggable = true;
  pane.ondragstart = function() {doDragStart(this)};
  pane.ondragend = function() {doDragEnd(this)};
  pane.ondragover = function(event) {doDragOver(event, this)};
  pane.ondrop = function(event) {doDrop(event)};
  pane.style.position = "relative";
}

function doDragStart(pane) {
  toDrag = pane;
}

function doDragEnd(pane) {
  toDrag = null; // For garbage collection
}

function doDragOver(event, item) {
  event.preventDefault();
  if (item == toDrag) {
    return;
  }
  var details = item.parentNode;
  if (details != toDrag.parentNode) {
    return;  // Don't drag into a different gap
  }
  var tar = event.target;
  var eventY = event.offsetY;
  if (tar != item) {
    eventY += tar.offsetTop;
  }
  if (2 * eventY < item.offsetHeight) {
    if (toDrag.nextSibling != item) {
      details.removeChild(toDrag);
      details.insertBefore(toDrag, item);
    }
  } else {
    var next = item.nextSibling;
    if (next != toDrag) {
      details.removeChild(toDrag);
      details.insertBefore(toDrag, next);
    }
  }
}

function doDrop(event) {
  event.preventDefault();
}

function makeDefineGoalPane(toDef) {
  var p = document.createElement("DIV");
  var d = makeData(p);
  d.kind = defineGoal;
  d.toDef = toDef;
  p.appendChild(makeVariantPane(textToElemHTML(varToText(toDef) + "=?", "div", false), define));
  return p;
}

function makeVariantPane(strHTML, variant) {
  var p = document.createElement("DIV");
  p.className = "pad-left";
  p.style.display = "flex";
  var d = makeData(p);
  d.variant = variant;
  var s;
  if (variant > 0) {
    s = "<div class='formula' style='margin-left: " + bulletIndent + "em; margin-right: " + bulletMargin + "em'>\u25CB</div>";
  } else {
    s = "<div class='formula' style='margin-right: " + bulletMargin + "em'>\u25CF</div>";
  }
  p.innerHTML = s + strHTML;
  p.onclick = function(event) {toggleVariantSelected(event, this)};
  p.ondblclick = function(event) {variantDblClicked(event, this)};
  return p;
}

function copyStmnt(stmnt) {
  var n = stmntCopyTable.length;
  var i;
  for (i = 0; i < n; i++) {
    if (stmntCopyTable[i].old == stmnt) {
      return stmntCopyTable[i].new;
    }
  }
  var copy = cloneStmnt(stmnt);
  stmntCopyTable.push({old: stmnt, new: copy});
  return copy;
}

function copyStmntList(stmntList) {
  var copy = [];
  var n = stmntList.length;
  var i;
  for (i = 0; i < n; i++) {
    copy.push(copyStmnt(stmntList[i]));
  }
  return copy;
}

function makeHeading(headingText) {  // For adding "Givens:" and "Goal:" headings to details pane
  var heading = document.createElement("DIV");
  heading.style.marginLeft = headingIndent + "em";
  heading.innerHTML = "<b>" + headingText + "</b>";
  return heading;
}

// stmnts should be array of statememnts containing at least one statement.
function addStmntListHTML(str, stmnts) {
  var i;
  str += textToElemHTML(stmnts[0][0].theText, "span", true);
  var last = stmnts.length - 1;
  if (last == 0) {
    return str;
  }
  if (last > 1) {
    for (i = 1; i < last; i++) {
      str += ", " + textToElemHTML(stmnts[i][0].theText, "span", true);
    }
    str += ",";
  }
   return str + " and " + textToElemHTML(stmnts[last][0].theText, "span", true);
}

function addVarListHTML(str, vars) {
  var i;
  str += textToElemHTML(varToText(vars[0]), "span", false);
  var last = vars.length - 1;
  if (last == 0) {
    return str;
  }
  if (last > 1) {
    for (i = 1; i < last; i++) {
      str += ", " + textToElemHTML(varToText(vars[i]), "span", false);
    }
    str += ",";
  }
   return str + " and " + textToElemHTML(varToText(vars[last]), "span", false);
}

function proofHereTextHTML(stmnt) {
  if (stmnt == null) {
    return "Proof of contradiction goes here.";
  } else {
    return "Proof of " + textToElemHTML(stmnt[0].theText, "span", true) + " goes here.";
  }
}

function definitionHereTextHTML(toDef) {
  return "Definition of " + textToElemHTML(varToText(toDef), "span", false) + " goes here.";
}

function thereforeTextHTML(stmnt) {
	if (stmnt == null) {
		return "Therefore we have reached a contradiction.";
	} else {
    return "Therefore " + textToElemHTML(stmnt[0].theText, "span", true);
	}
}

function sinceTextHTML(usedStmnts, inferred) {
	var s;
	if (usedStmnts == null) {
		s = "Therefore ";
	} else {
    s = addStmntListHTML("Since ", usedStmnts) + ", ";
	}
	if (inferred == null) {
		s += "we have reached a contradiction.";
	} else {
    s = addStmntListHTML(s, inferred) + ".";
	}
	return s;
}

function supposeTextHTML(prems) {
  return addStmntListHTML("Suppose ", prems) + ".";
}

// Only call this if subproofs != noSubproofs
function getProofRange(inf) {
  if (getData(inf).subproofs == subproofsFirst) {
    return {first: 0, last: inf.childNodes.length - 2};
  } else {
    return {first: 1, last: inf.childNodes.length - 1};
  }
}

function numGivens(kind, details) {
  if (kind == noGoalGap) {
    return details.childNodes.length - 1;
  } else {
    return details.childNodes.length - 3;
  }
}

function getGap(varPane) {
  return varPane.parentNode.parentNode.parentNode.parentNode;
}

function getVarKind(varPane) {
  return getData(varPane.parentNode).kind;
}

// Only call on varPane of given or goal, not defineGoal.
function getForm(varPane) {
  return getData(varPane.parentNode).theStmnt[getData(varPane).variant].theForm;
}

// Only call this on a goal gap
function getGoal(gap) {
  return getData(gap.firstChild.lastChild.lastChild).theStmnt;
}

// Only call this on a define goal gap
function getDefineGoal(gap) {
  return getData(gap.firstChild.lastChild.lastChild).toDef;
}

function getProof(step) {
  var pf = step.parentNode;
  if (pf == mainProof) {
    return pf;
  }
  return pf.parentNode;
}

function getConclusion() { // Get conclusion of mainProof
  var lastStep = mainProof.lastChild;
  var stepData = getData(lastStep);
  if (stepData.kind == inference) {
    var lastInferred = stepData.inferred;
    return (lastInferred == null) ? null : lastInferred[0];
  } else {
    return getGoal(lastStep)
  }
}


function toggleDetails(event, gap) {
  if (openMenu != null) {
    return;
  }
  var details = gap.firstChild.lastChild;
  if (details.classList.contains("hide")) {
    details.classList.remove("hide");
  } else {
    details.classList.add("hide");
    if ((selectedStep == gap) && (selection.length > 0)) {
      clearSelection();
    }
  }
  event.stopPropagation();
}

function toggleSteps(event, proof) {
  if (openMenu != null) {
    return;
  }
  var stepsPane = proof.lastChild;
  var dotsPane = stepsPane.previousSibling;
  if (stepsPane.classList.contains("hide")) {
    stepsPane.classList.remove("hide");
    dotsPane.classList.add("hide");
  } else {
    stepsPane.classList.add("hide");
    dotsPane.classList.remove("hide");
    if (selectedStep != null) {
      var p = selectedStep.parentNode;
      while (true) {
        if (p == mainProof) {
          break;
        }
        p = p.parentNode;
        if (p == proof) {
          clearSelection();
          break;
        }
        p = p.parentNode.parentNode;
      }
    }
  }
  event.stopPropagation();
}

function clearSelection() {
	if (selectedStep == null) {
		return;
	}
	if (selection.length == 0) {
		if (getData(selectedStep).kind == inference) {
      selectedStep.classList.remove("selected");
    } else {  // Gap: only frame is highlighted
      selectedStep.firstChild.classList.remove("selected");
    }
	} else {
    var i;
		for (i = 0; i < selection.length; i++) {
      selection[i].classList.remove("selected");
		}
		selection.length = 0;
	}
  selectedStep = null;
}

function toggleStepSelected(event, step) {
  if (openMenu != null) {
    return;
  }
  if ((selectedStep == step) && (selection.length == 0)) {
    clearSelection();
  } else {
    clearSelection();
    selectedStep = step;
    if (getData(step).kind == inference) {
      step.classList.add("selected");
    } else {
    step.firstChild.classList.add("selected");
    }
  }
  if (event != null) {
    event.stopPropagation();
  }
}

function toggleVariantSelected(event, varPane) {
  var i;
  var l = selection.length;
	var g = getGap(varPane);
  if (openMenu != null) {
    return;
  }
  event.stopPropagation();
	if ((g != selectedStep) || (l == 0)) {
		selectVariant(varPane);
		return;
  }
  for (i = 0; i < l; i++) {
    if (selection[i] == varPane) {
      if (l == 1) {
        clearSelection();
      } else {
        varPane.classList.remove("selected");
        selection.splice(i, 1);
      }
      return;
    }
  }
  var firstSelected = selection[0];
  if (getVarKind(varPane) == given) {
    selection.push(varPane);
  } else if (getVarKind(firstSelected) == given) {
    selection.splice(0, 0, varPane);
  } else {
    firstSelected.classList.remove("selected");
    selection[0] = varPane;
  }
  varPane.classList.add("selected");
}


function selectVariant(varPane) {
	clearSelection();
	selectedStep = getGap(varPane);
  selection.push(varPane);
  varPane.classList.add("selected");
}

function variantDblClicked(event, varPane) {
  selectVariant(varPane);
  if (getData(varPane).variant == define) {
    doDefine();
  } else {
    doReexSub(true);
  }
  event.stopPropagation();
}
