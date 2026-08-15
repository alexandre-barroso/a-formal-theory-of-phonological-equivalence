function pushBlock(kind, name) {
  depth++
  blockKind[depth] = kind
  previousNamespace[depth] = currentNamespace
  if (kind == "namespace") {
    if (currentNamespace == "" || name ~ /^PhonologicalCalculus(\.|$)/) {
      currentNamespace = name
    } else {
      currentNamespace = currentNamespace "." name
    }
  }
}

function popBlock() {
  if (depth > 0) {
    currentNamespace = previousNamespace[depth]
    delete blockKind[depth]
    delete previousNamespace[depth]
    depth--
  }
}

BEGIN {
  depth = 0
  currentNamespace = ""
}

/^[[:space:]]*namespace[[:space:]]+[A-Za-z0-9_.]+[[:space:]]*$/ {
  line = $0
  sub(/^[[:space:]]*namespace[[:space:]]+/, "", line)
  sub(/[[:space:]]*$/, "", line)
  pushBlock("namespace", line)
  next
}

/^[[:space:]]*(noncomputable[[:space:]]+)?section([[:space:]]+[A-Za-z0-9_.]+)?[[:space:]]*$/ {
  pushBlock("section", "")
  next
}

/^[[:space:]]*end([[:space:]]+[A-Za-z0-9_.]+)?[[:space:]]*$/ {
  popBlock()
  next
}

{
  declaration = $0
  sub(/^[[:space:]]*/, "", declaration)

  while (declaration ~ /^@\[[^]]+\][[:space:]]*/) {
    sub(/^@\[[^]]+\][[:space:]]*/, "", declaration)
  }

  if (declaration ~ /^private[[:space:]]+/) next

  while (declaration ~ /^(protected|noncomputable)[[:space:]]+/) {
    sub(/^(protected|noncomputable)[[:space:]]+/, "", declaration)
  }

  if (declaration !~ /^(theorem|lemma)[[:space:]]+/) next

  sub(/^(theorem|lemma)[[:space:]]+/, "", declaration)
  name = declaration
  sub(/[[:space:]({:].*$/, "", name)

  if (name ~ /^PhonologicalCalculus\./ || currentNamespace == "") {
    print name
  } else {
    print currentNamespace "." name
  }
}
