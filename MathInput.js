//Utililty functions for math input field
"use strict";

function initMathPal() {
  mathPal = document.createElement("DIV");
  mathPal.className = "tableGrid";
  mathPal.style.gridTemplateColumns = "repeat(12, max-content)";
  var instrCell = document.createElement("DIV");
  instrCell.style.gridRowStart = "1";
  instrCell.style.gridRowEnd = "3";
  instrCell.style.marginRight = "0.66em";
  instrCell.appendChild(document.createTextNode("Click here to enter these symbols:"));
  mathPal.appendChild(instrCell);
  appendSymbolButton(symbols[all].letter, "for all (Alt+Shift+A)");
  appendSymbolButton(symbols[exist].letter, "there exists (Alt+Shift+E)");
  appendSymbolButton(symbols[conj].letter, "and (Alt+A)");
  appendSymbolButton(symbols[disj].letter, "or (Alt+O)");
  appendSymbolButton(symbols[cond].letter, "conditional (Alt+C)");
  appendSymbolButton(symbols[bicond].letter, "biconditional (Alt+B)");
  appendSymbolButton(symbols[neg].letter, "not (Alt+F, for False)");
  appendSymbolButton(symbols[symmDiff].letter, "symmetric difference (Alt+D)");
  appendSymbolButton(symbols[diff].letter, "set difference");
  appendSymbolButton(symbols[prod].letter, "cartesian product (Alt+P)");
  appendSymbolButton(symbols[comp].letter, "composition (of relations) (Alt+Shift+C)");
  appendSymbolButton(symbols[equals].letter, "equals");
  appendSymbolButton(symbols[notEquals].letter, "not equals (Alt+=)");
  appendSymbolButton(symbols[element].letter, "element of (Alt+M, for Member of)");
  appendSymbolButton(symbols[notElement].letter, "not an element of (Alt+Shift+M)");
  appendSymbolButton(symbols[subset].letter, "subset of (Alt+S)");
  appendSymbolButton(symbols[notSubset].letter, "not a subset of (Alt+Shift+S)");
  appendSymbolButton(symbols[intr].letter, "intersection (Alt+Shift+I)");
  appendSymbolButton(symbols[union].letter, "union (Alt+Shift+U)");
  appendSymbolButton(symbols[power].letter, "power set (Alt+Shift+P)");
  appendSymbolButton(symbols[empty].letter, "empty set (Alt+0)");
  appendSupSymbolButton(symbols[inverse].letter, "inverse (of a relation) (Alt+1)");
}

function appendSymbolButton(c, tooltip) {
  var b = document.createElement("BUTTON");
  mathPal.append(b);
  b.outerHTML = "<button class=\"pal\" title=\"" + tooltip + "\" onclick=\"inputChar('"
  + c + "')\">" + c + "</button>";
}

function appendSupSymbolButton(c, tooltip) {
  var b = document.createElement("BUTTON");
  mathPal.append(b);
  b.outerHTML = "<button class=\"pal\" title=\"" + tooltip + "\" onclick=\"inputChar('"
  + c + "', 'SUP')\"><sup>" + c + "</sup></button>";
}

function makeMathField() {
  var theField = document.createElement("DIV");
  theField.className = "math-input";
  theField.tabIndex = 0;
  theField.contentEditable = true;
  theField.ondragenter = function() {return false};
  theField.ondragover = function() {return false};
  theField.ondrop = function() {return false};
  theField.onpaste = function() {return false};
  theField.onkeydown = processKeyDown;
  theField.onfocus = function() {fieldFocus(this)};
  theField.onblur = function() {fieldBlur(this)};
  theField.onmousedown = function(event) {if (!event.shiftKey) {window.getSelection().empty()}};
  makeData(theField).adjustMySel = null;
  return theField;
}

function setMySel() {
  var sel = window.getSelection();
  var an = sel.anchorNode;
  var fn = sel.focusNode;
  if ((an == null) || (fn == null)) {
    mySel.theField = null;
    return;
  }
  var mathFields = document.getElementsByClassName("math-input");
  var len = mathFields.length;
  var found = false;
  var field;
  var i = 0;
  while ((i < len) && !found) {
    field = mathFields[i];
    found = (an == field) || field.contains(an);
    i++;
  }
  if (!found || ((fn != field) && !field.contains(fn))) {
    mySel.theField = null;
  } else {
    mySel.orig = sel;
    mySel.theField = field;
    var aPos = selEndPos(mySel.theField, mySel.orig.anchorNode, mySel.orig.anchorOffset);
    var fPos = selEndPos(mySel.theField, mySel.orig.focusNode, mySel.orig.focusOffset);
    if ((aPos.outer < fPos.outer) || ((aPos.outer == fPos.outer) && (aPos.inner < fPos.inner))) {
      if (fPos.inner > 0) {
        fPos.outer++;
      }
      mySel.aOffset = aPos.outer;
      mySel.fOffset = fPos.outer;
      mySel.start = aPos.outer;
      mySel.end = fPos.outer;
    } else {
      if (aPos.inner > 0) {
        aPos.outer++;
      }
      mySel.aOffset = aPos.outer;
      mySel.fOffset = fPos.outer;
      mySel.start = fPos.outer;
      mySel.end = aPos.outer;
    }
    var adjustFunc = getData(field).adjustMySel;
    if (adjustFunc != null) {
      adjustFunc();
    }
  }
}

function selEndPos(field, node, offset) {
  if (node == field) {
    return {outer: offset, inner: 0};
  }
  var fieldChild;
  if (node.parentNode == field) {
    fieldChild = node;
  } else {
    fieldChild = node.parentNode;
  }
  var c = field.childNodes;
  var i = 0;
  while (c[i] != fieldChild) {
    i++;
  }
  if (node == fieldChild) {
    if (offset > 0) {
      i++;
    }
    return {outer: i, inner: 0}
  }
  if (offset == node.textContent.length) {
    return {outer: i+1, inner: 0};
  }
  return {outer: i, inner: offset};
}

function highlightMySel() {
   var chrs = mySel.theField.childNodes;
  var i;
  for (i = 0; i < mySel.start; i++) {
    chrs[i].classList.remove("selected");
  }
  for (i = mySel.start; i < mySel.end; i++) {
    chrs[i].classList.add("selected");
  }
  for (i = mySel.end; i < chrs.length; i++) {
    chrs[i].classList.remove("selected");
  }
}

function updateSelection(field, anchor, focus) {
  var sel = window.getSelection();
  sel.setBaseAndExtent(field, anchor, field, focus);
  // Rest just in case selectionchange event doesn't fire
  mySel.orig = sel;
  mySel.theField = field;
  mySel.aOffset = anchor;
  mySel.fOffset = focus;
  if (anchor < focus) {
    mySel.start = anchor;
    mySel.end = focus;
  } else {
    mySel.start = focus;
    mySel.end = anchor;
  }
  highlightMySel();
}

function selectWholeField(field) {
  updateSelection(field, 0, field.childNodes.length);
}

function fieldFocus(field) {
  setMySel();
  if (mySel.theField == field) {
    highlightMySel();
  } else {
    updateSelection(field, field.childNodes.length, field.childNodes.length);
  }
}

function fieldBlur(field) {
  var chrs = field.childNodes;
  var i;
  for (i = 0; i < chrs.length; i++) {
    chrs[i].classList.remove("selected");
  }
}

function fixSelection() {
  setMySel();
  if (mySel.theField != null) {
    highlightMySel();
  }
}

function removeInput(field, start, end) {
  var i = start;
  while (i < end) {
    field.removeChild(field.childNodes[start]);
    i++;
  }
}

function removeAllInput(field) {
  field.innerHTML = "";
  updateSelection(field, 0, 0);   //Shouldn't be necessary but Safari seems to need it.
}

function inputCharToSel(c, tag = "SPAN") {
  var n = document.createElement(tag);
  n.textContent = c;
  var f = mySel.theField;
  var s = mySel.start;
  var e = mySel.end;
  removeInput(f, s, e);
  if (s == f.childNodes.length) {
    f.appendChild(n);
  } else {
    f.insertBefore(n, f.childNodes[s]);
  }
  updateSelection(f, s+1, s+1);
  if (f.oninput != null) {
    f.oninput();
  }
}

function inputChar(c, tag = "SPAN") {
  setMySel();
  if (mySel.theField != null) {
    inputCharToSel(c, tag);
  }
}

function processKeyDown(event) {
  if (event.ctrlKey || event.metaKey) {
    return;
  }
  var theKey = event.key;
  if (theKey == "Tab") {
    return;
  }
  setMySel();
  if (mySel.theField == null) {  // Will this ever happen?  It shouldn't.
    return;
  }
  var f = mySel.theField;
  var s = mySel.start;
  var e = mySel.end;
  if (theKey == "Backspace") {
    if ((s == e) && (s > 0)) {
        s--;
    }
    if (s < e) {
      removeInput(f, s, e);
      updateSelection(f, s, s);
      if (f.oninput != null) {
        f.oninput();
      }
    }
  } else if (theKey == "ArrowLeft") {
    if (event.shiftKey) {
      if (mySel.fOffset > 0) {
        mySel.fOffset--;
        updateSelection(f, mySel.aOffset, mySel.fOffset);
      }
    } else {
      if ((s > 0) && (s == e)) {
        s--;
      }
      e = s;
      updateSelection(f, s, e);
    }
  } else if (theKey == "ArrowRight") {
    if (event.shiftKey) {
      if (mySel.fOffset < f.childNodes.length) {
        mySel.fOffset++;
        updateSelection(f, mySel.aOffset, mySel.fOffset);
      }
    } else {
      if ((e < f.childNodes.length) && (s == e)) {
        e++;
      }
      s = e;
      updateSelection(f, s, e);
    }
  } else if (theKey.length == 1) {
    if (event.altKey) {
      switch (event.code) {
        case "KeyA":
          if (event.shiftKey) {
            inputCharToSel(symbols[all].letter);
          } else {
            inputCharToSel(symbols[conj].letter);
          }
          break;
        case "KeyO":
          if (!event.shiftKey) {
            inputCharToSel(symbols[disj].letter);
          }
          break;
        case "KeyC":
          if (event.shiftKey) {
            inputCharToSel(symbols[comp].letter);
          } else {
            inputCharToSel(symbols[cond].letter);
          }
          break;
        case "KeyB":
          if (!event.shiftKey) {
            inputCharToSel(symbols[bicond].letter);
          }
          break;
        case "KeyF":
          if (!event.shiftKey) {
            inputCharToSel(symbols[neg].letter);
          }
          break;
        case "KeyE":
          if (event.shiftKey) {
            inputCharToSel(symbols[exist].letter);
          }
          break;
        case "KeyM":
          if (event.shiftKey) {
            inputCharToSel(symbols[notElement].letter);
          } else {
            inputCharToSel(symbols[element].letter);
          }
          break;
        case "KeyS":
          if (event.shiftKey) {
            inputCharToSel(symbols[notSubset].letter);
          } else {
            inputCharToSel(symbols[subset].letter);
          }
          break;
        case "Equal":
          if (!event.Shift) {
            inputCharToSel(symbols[notEquals].letter);
          }
          break;
        case "KeyI":
          if (event.shiftKey) {
            inputCharToSel(symbols[intr].letter);
          }
          break;
        case "KeyU":
          if (event.shiftKey) {
            inputCharToSel(symbols[union].letter);
          }
          break;
        case "KeyD":
          if (!event.shiftKey) {
            inputCharToSel(symbols[symmDiff].letter);
          }
          break;
        case "KeyP":
          if (event.shiftKey) {
            inputCharToSel(symbols[power].letter);
          } else {
            inputCharToSel(symbols[prod].letter);
          }
          break;
        case "Digit0":
          if (!event.shiftKey) {
            inputCharToSel(symbols[empty].letter);
          }
          break
        case "Digit1":
          if (!event.shiftKey) {
            inputCharToSel(symbols[inverse].letter, "SUP");
          }
      }
    } else {
      if ((("a" <= theKey) && ("z" >= theKey)) || (("A" <= theKey) && ("Z" >= theKey))) {
        inputCharToSel(theKey, "I");
      } else if (("0" <= theKey) && ("9" >= theKey)) {
        inputCharToSel(theKey, "SUB");
      } else if (theKey == "\\") {
        inputCharToSel(symbols[diff].letter);
      } else if (theKey != " ") {
        inputCharToSel(theKey);
      }
    }
  }
  event.preventDefault();
}
