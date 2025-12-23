macro doc:(docComment)? "lemma" n:declId sig:declSig val:declVal : command =>
  `($[$doc:docComment]? theorem $n $sig $val)
