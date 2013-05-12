Theorem hoare_asgn : forall Q X a,
  {{assn_sub X a Q}} (X ::= a) {{Q}}.