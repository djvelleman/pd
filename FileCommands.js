// Functions for reading and writing files
"use strict";

function doNewTheorem() {
  doEntryDialog(null, null);
}

function doReviseTheorem() {
  var proofData = getData(mainProof);
  var prem = proofData.premises;
  var l = prem.length;
  var currPrem = [];
  var i;
  for (i = 0; i < l; i++) {
    currPrem.push(cloneFormWithText(prem[i][0]));
  }
  doEntryDialog(currPrem, cloneFormWithText(getConclusion()[0]));
}

function doEntryDialog(currPrem, currConc) {
  var entryDialog;
  var mathField;
  var hypList, hypListWidth;
  var conc, concFormWithText;
  var addHypButton, cutHypButton, setConcButton, OKButton, cancelButton, OKCancelPanel;
  var selectedHyp = null;

  function fixButtons() {
    addHypButton.disabled = (mathField.childNodes.length == 0);
    setConcButton.disabled = addHypButton.disabled;
    cutHypButton.disabled = (selectedHyp == null);
    OKButton.disabled = (concFormWithText == null);
  }

  function selectHyp(e) {
    if (selectedHyp != null) {
      selectedHyp.classList.remove("selected");
    }
    selectedHyp = e;
    e.classList.add("selected");
    if (mathField.childNodes.length == 0) {
      mathField.innerHTML = textToHTML(getData(e).formWithText.theText, false);
    }
    fixButtons();
    mathField.focus();
  }

  function doAddHyp() {
    var form = parse(mathField, bool);
    if (form == null) {
      return;
    }
    installHyp({theForm: form, theText: form.toText()});
    removeAllInput(mathField);
    fixButtons();
    mathField.focus();
  }

  function installHyp(fwt) {
    var elem = textToElem(fwt.theText, "DIV", false);
    var hypData = makeData(elem);
    hypData.formWithText = fwt;
    elem.onclick = function() {selectHyp(this)};
    elem.classList.add("list-element");
    elem.style.width = hypListWidth + "px";
    elem.style.height = (lineHeight + 0.1) + "em";
    hypList.appendChild(elem);
  }

  function doCutHyp() {
    hypList.removeChild(selectedHyp);
    selectedHyp = null;
    fixButtons();
    mathField.focus();
  }

  function doSetConc() {
    var form = parse(mathField, bool);
    if (form == null) {
      return;
    }
    installConc({theForm: form, theText: form.toText()});
    removeAllInput(mathField);
    fixButtons();
    mathField.focus();
  }

  function installConc(fwt) {
    conc.innerHTML = textToHTML(fwt.theText, true);
    concFormWithText = fwt;
  }

  function concClicked() {
    if ((mathField.childNodes.length == 0) && (concFormWithText != null)) {
      mathField.innerHTML = textToHTML(concFormWithText.theText, false);
    }
    fixButtons();
    mathField.focus();
  }

  function setUpProof() {
    hideDialog();
    var premises = [];
    var defined = [];
    var fwt;
    var premElems = hypList.childNodes;
    var numprem = premElems.length;
    var i;
    for (i = 0; i < numprem; i++) {
      fwt = getData(premElems[i]).formWithText;
      premises.push([fwt]);
      fwt.theForm.addVars(defined, true);
    }
    concFormWithText.theForm.addVars(defined, true);
    var conclusion = [concFormWithText];
    var thmString = "<b>Theorem.</b> ";
    if (numprem > 0) {
      thmString = addStmntListHTML(thmString + "Suppose ", premises) + ". Then ";
    }
    thmString += textToElemHTML(concFormWithText.theText, "span", true) + ".<br><b>Proof:</b>";
    var newProof = makeProof(defined, premises, "", 0);
    newProof.appendChild(makeGoalGap(defined.slice(0), premises.slice(0), conclusion));  // slice(0) copies the array.
    installProof(thmString, newProof);
  }
  
  entryDialog = makeDialog(42);
  entryDialog.appendChild(mathPal);
  entryDialog.appendChild(makeTextPane("Enter hypotheses and conclusion here:", 0.66, 0.33));
  mathField = makeMathField();
  entryDialog.appendChild(mathField);
  var d = document.createElement("DIV");
  d.className = "tableGrid";
  d.style.gridTemplateColumns = "max-content auto";
  d.style.justifyContent = "stretch";
  d.style.margin = "0.66em 0em";
  var d2 = document.createElement("DIV");
  addHypButton = makeButton("Add Hypothesis");
  addHypButton.onclick = doAddHyp;
  cutHypButton = makeButton("Cut Hypothesis");
  cutHypButton.onclick = doCutHyp;
  d2.appendChild(addHypButton);
  d2.appendChild(document.createElement("BR"));
  d2.appendChild(document.createElement("BR"));
  d2.appendChild(cutHypButton);
  d.appendChild(d2);
  d2 = document.createElement("DIV");
  d2.appendChild(document.createTextNode("Hypotheses:"));
  hypList = document.createElement("DIV");
  hypList.className = "list-pane";
  hypList.style.height = (6 * (lineHeight + 0.1)) + "em";
  d2.appendChild(hypList);
  d.appendChild(d2);
  d2 = document.createElement("DIV");
  setConcButton = makeButton("Set Conclusion");
  setConcButton.onclick = doSetConc;
  d2.appendChild(setConcButton);
  d.appendChild(d2);
  d2 = document.createElement("DIV");
  d2.appendChild(document.createTextNode("Conclusion:"));
  conc = document.createElement("DIV");
  conc.className = "formula";
  conc.style.height = (2 * lineHeight) + "em";
  conc.style.overflow = "hidden";
  conc.onclick = concClicked;
  d2.appendChild(conc);
  d.appendChild(d2);
  entryDialog.appendChild(d);
  OKCancelPanel = makeButtonPanel(["OK", "Cancel"]);
  OKButton = OKCancelPanel.firstChild;
  cancelButton = OKButton.nextSibling;
  entryDialog.appendChild(OKCancelPanel);
  cancelButton.onclick = function() {hideDialog()};
  OKButton.onclick = setUpProof;
  mathField.oninput = fixButtons;
  if (currPrem != null) {
    var i;
    for (i = 0; i < currPrem.length; i++) {
      installHyp(currPrem[i]);
    }
    installConc(currConc);
  } else {
    concFormWithText = null;
  }
  fixButtons();
  showDialog(entryDialog, OKButton, true);
  mathField.focus();
  hypListWidth = hypList.clientWidth;
}

function doSave() {
  var myFile, myURL, s, i, j, data, stmntList;

  function findStmnts(steps) {
    var i, stepData;
    var nextStep = steps.firstChild;
    do {
      stepData = getData(nextStep);
      if (stepData.kind == inference) {
        if (stepData.inferred != null) {
          addSetToSet(stmntList, stepData.inferred);
        }
        if (stepData.subproofs != noSubproofs) {
          var c = nextStep.childNodes;
          var proofRange = getProofRange(nextStep);
          for (i = proofRange.first; i <= proofRange.last; i++) {
            var subpf = c[i];
            var pfData = getData(subpf);
            if (pfData.premises != null) {
              addSetToSet(stmntList, pfData.premises);
            }
            findStmnts(subpf.lastChild);
          }
        }
      } else if (stepData.kind == goalGap) {
        var theGoal = getGoal(nextStep);
        if (theGoal != null) {
          addElemToSet(stmntList, theGoal);
        }
      }
      nextStep = nextStep.nextSibling;
    } while (nextStep != null);
  }

  function addNumList(list) {
    if (list == null) {
      s += "-\n";
      return;
    }
    if (list.length == 0) {
      s+= "\n";
      return;
    }
    s += list[0].toString();
    var i;
    for (i = 1; i < list.length; i++) {
      s += ("," + list[i].toString());
    }
    s += "\n";
  }

  function addStmntList(list) {
    if (list == null) {
      s += "-\n";
      return;
    }
    if (list.length == 0) {
      s += "\n";
      return;
    }
    s += stmntList.indexOf(list[0]).toString();
    var i;
    for (i = 1; i < list.length; i++) {
      s += ("," + stmntList.indexOf(list[i]).toString());
    }
    s += "\n";
  }

  function addGGPane(thePane) {
    var theStmnt = getData(thePane).theStmnt;
    if (theStmnt == null) {
      s += "C\n";
      return;
    }
    s += (stmntList.indexOf(theStmnt).toString() + "\n");
    var varPane = thePane.firstChild;
    s += getData(varPane).variant.toString();
    varPane = varPane.nextSibling;
    while (varPane != null) {
      s += ("," + getData(varPane).variant.toString());
      varPane = varPane.nextSibling;
    }
    s += "\n";
  }

  function addSteps(stepsPane) {
    var i, c;
    var nextStep = stepsPane.firstChild;
    do {
      var stepData = getData(nextStep);
      s += (stepData.kind.toString() + "\n");
      addNumList(stepData.defined);
      if (stepData.kind == inference) {
        addStmntList(stepData.used);
        addStmntList(stepData.inferred);
        var subproofs = stepData.subproofs;
        s += (subproofs.toString() + "\n");
        if (subproofs == subproofsFirst) {
          s += (nextStep.lastChild.innerHTML + "\n");
        } else {
          s += (nextStep.firstChild.innerHTML + "\n");
        }
        if (subproofs != noSubproofs) {
          c = nextStep.childNodes;
          var proofRange = getProofRange(nextStep);
          for (i = proofRange.first; i <= proofRange.last; i++) {
            var subpf = c[i];
            var subpfData = getData(subpf);
            addNumList(subpfData.defined);
            addStmntList(subpfData.premises);
            s += (subpfData.casePrefix + "\n" + subpfData.lemmaDepth.toString() + "\n");
            var showHide = subpf.firstChild;
            var introPane = showHide.nextSibling;
            var dotsPane = introPane.nextSibling;
            s += (introPane.innerHTML + "\n" + dotsPane.innerHTML + "\n");
            s += (showHide.classList.contains("complete") ? "1\n" : "0\n");
            s += (dotsPane.classList.contains("hide") ? "0\n" : "1\n");
            addSteps(dotsPane.nextSibling);
          }
        }
        s += "</inf>\n";
      } else {
        var detailsPane = nextStep.firstChild.lastChild;
        s += (detailsPane.previousSibling.innerHTML + "\n");
        s += (detailsPane.classList.contains("hide") ? "1\n" : "0\n");
        if (stepData.kind == goalGap) {
          addGGPane(detailsPane.lastChild);
        } else if (stepData.kind == defineGoalGap) {
          s += (getData(detailsPane.lastChild).toDef.toString() + "\n");
        }
        var numG = numGivens(stepData.kind, detailsPane);
        c = detailsPane.childNodes;
        for (i = 1; i <= numG; i++) {
          addGGPane(c[i]);
        }
        s += "</gap>\n";
      }
      nextStep = nextStep.nextSibling;
    } while (nextStep != null);
    s += "</proof>\n";
  }

  data = getData(mainProof);
  stmntList = data.premises.slice(0);
  findStmnts(mainProof);
  s = "";
  for (i = 0; i < stmntList.length; i++) {
    var theStmnt = stmntList[i];
    for (j = 0; j < theStmnt.length; j++) {
      s += theStmnt[j].theText + "\n";
    }
    s += "</stmnt>\n";
  }
  s += "</stmntList>\n";
  s += document.getElementById("theorem").innerHTML + "\n";
  addNumList(data.defined);
  addStmntList(data.premises);
  addSteps(mainProof);
  myFile = new Blob([s], {type: "text/plain"}); // maybe add:  endings: "native" 
  myURL = URL.createObjectURL(myFile);

  var anchor = document.createElement("A");
  anchor.href = myURL;
  anchor.download = "PDProof.txt";
  anchor.click();
  URL.revokeObjectURL(myURL);

/* // Alternative method.  Works in Safari but not Firefox or Chrome
  var newWindow = window.open(myURL);
  URL.revokeObjectURL(myURL);
  newWindow.alert("Click OK and then use your browser's Save command to save the contents of this window in a file.");
  */

}

function doOpen() {
  var okButton, fileInput, theoremHTML, newProof;

  function startRead() {
    var reader = new FileReader();
    reader.readAsText(fileInput.files[0]);
    reader.onload = function() {readFile(reader.result)};
  }
  
  function readFile(result) {
    var stmntList = [];
    var line, stmnt, numStmnt;
    const maxVar = 52051;
  
    function nextLine() {
      var i = result.indexOf("\n");
      if (i == -1) {
        throw "File ended unexpectedly.";
      } else {
        line = result.substring(0, i);
        result = result.substring(i + 1);
      }
    }

    function getNum(str, max) {
      var n = parseInt(str);
      if ((0 <= n) && (n <= max)) {
        return n;
      }
      throw "Illegal number: " + n + " is not between 0 and " + max + ".";
    }

    function getNumList(max) {
      if (line == "-") {
        return null;
      }
      var result = [];
      if (line == "") {
        return result;
      }
      var i = line.indexOf(",");
      while (i != -1) {
        result.push(getNum(line.substring(0, i), max));
        line = line.substring(i + 1);
        i = line.indexOf(",");
      }
      result.push(getNum(line, max));
      return result;
    }

    function getStmntList() {
      function getStmnt(str) {
        var n = parseInt(str);
        if (!((0 <= n) && (n <= numStmnt))) {
          throw "Illegal statement number: " + n + ".";
        }
        return stmntList[n];
      }

      if (line == "-") {
        return null;
      }
      var result = [];
      if (line == "") {
        return result;
      }
      var i = line.indexOf(",");
      while (i != -1) {
        result.push(getStmnt(line.substring(0, i)));
        line = line.substring(i + 1);
        i = line.indexOf(",");
      }
      result.push(getStmnt(line));
      return result;
    }

    function getGGPane(paneKind) {
      if (line == "C") {
        return makeGGPane(goal, null);
      }
      var theStmnt = stmntList[getNum(line, numStmnt)];
      var p = makeGGPane(paneKind, theStmnt);
      nextLine();
      var variantList = getNumList(theStmnt.length - 1);
      var varPane = p.firstChild.nextSibling;
      while (varPane != null) {
        var nextPane = varPane.nextSibling;
        if (!variantList.includes(getData(varPane).variant)) {
          p.removeChild(varPane);
        }
        varPane = nextPane;
      }
      return p;
    }

    function getSteps(stepsPane) {
      var kind, defined, used, inferred, subproofs, infHTML, inf, infData, premises;
      var casePrefix, lemmaDepth, introHTML, dotsHTML, subpf, infPane, subpfSteps;
      var gap, detailsPane, goalPane;
      nextLine();
      do {
        kind = getNum(line, noGoalGap);
        nextLine();
        defined = getNumList(maxVar);
        nextLine();
        if (kind == inference) {
          used = getStmntList();
          nextLine();
          inferred = getStmntList();
          nextLine();
          subproofs = getNum(line, subproofsLast);
          nextLine();
          infHTML = line;
          inf = makeInference(defined, used, inferred, infHTML);
          nextLine();
          if (subproofs != noSubproofs) {
            infData = getData(inf);
            infData.subproofs = subproofs;
            infPane = inf.firstChild;
            do {
              defined = getNumList(maxVar);
              nextLine();
              premises = getStmntList();
              nextLine();
              casePrefix = line;
              nextLine();
              lemmaDepth = getNum(line, Number.MAX_SAFE_INTEGER);
              nextLine();
              introHTML = line;
              nextLine();
              dotsHTML = line;
              subpf = makeSubproofStruct(defined, premises, casePrefix, lemmaDepth, introHTML, dotsHTML);
              subpfSteps = subpf.lastChild;
              nextLine();
              if (getNum(line, 1) == 1) {
                subpf.firstChild.classList.add("complete");
              }
              nextLine();
              if (getNum(line, 1) == 1) {
                subpfSteps.classList.add("hide");
                subpfSteps.previousSibling.classList.remove("hide");
              }
              getSteps(subpfSteps);
              if (subproofs == subproofsFirst) {
                inf.insertBefore(subpf, infPane);
              } else {
                inf.appendChild(subpf);
              }
              nextLine();
            } while (line != "</inf>");
          } else {
            if (line != "</inf>") {
              throw "Illegal inference.";
            }
          }
          stepsPane.appendChild(inf);
        } else { // Gap
          introHTML = line;
          gap = makeGapStruct(kind, defined, introHTML);
          detailsPane = gap.firstChild.lastChild;
          nextLine();
          if (getNum(line, 1) == 1) {
            detailsPane.classList.add("hide");
          }
          if (kind == goalGap) {
            nextLine();
            goalPane = getGGPane(goal);
          } else if (kind == defineGoalGap) {
            nextLine();
            goalPane = makeDefineGoalPane(getNum(line, maxVar));
          }
          nextLine();
          while (line != "</gap>") {
            detailsPane.appendChild(getGGPane(given));
            nextLine();
          }
          if (kind != noGoalGap) {
            detailsPane.appendChild(makeHeading("Goal:"));
            detailsPane.appendChild(goalPane);
          }
          stepsPane.appendChild(gap);
        }
        nextLine();
      } while (line != "</proof>");
    }
  
    try {
      nextLine();
      while (line != "</stmntList>") {
        stmnt = [];
        do {
          var form = parse(textToElem(line, "span", false), bool, false);
          if (form == null) {
            throw "Illegal formula: " + line + ".";
          }
          stmnt.push({theForm: form, theText: form.toText()})
          nextLine();
        } while (line != "</stmnt>");
        stmntList.push(stmnt);
        nextLine();
      }
      numStmnt = stmntList.length;
      nextLine();
      theoremHTML = line;
      nextLine();
      var defined = getNumList(maxVar);
      nextLine();
      var premises = getStmntList();
      newProof = makeProof(defined, premises, "", 0);
      getSteps(newProof);
      if (result != "") {
        throw "Extra characters at end of file.";
      }
      okButton.disabled = false;
      okButton.focus();
    }
    catch(err) {
      showMessage("Error in file: " + err);
    }
  }

  function finishOpen() {
    hideDialog();
    installProof(theoremHTML, newProof);
  }

  var theDialog = makeDialog(20);
  theDialog.appendChild(makeTextPane("Choose a file to open.", 0, 0.66));
  fileInput = document.createElement("INPUT");
  fileInput.type = "file";
  fileInput.onchange = startRead;
  theDialog.appendChild(fileInput);
  var okCancelPanel = makeButtonPanel(["Open", "Cancel"]);
  okCancelPanel.style.marginTop = "1em";
  theDialog.appendChild(okCancelPanel);
  okButton = okCancelPanel.firstChild;
  var cancelButton = okButton.nextSibling;
  okButton.disabled = true; // Enable OK when read has been successful
  okButton.onclick = finishOpen;
  cancelButton.onclick = function() {hideDialog()};
  showDialog(theDialog, okButton, true);
}
