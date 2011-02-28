

newPackage(
    "NCF",
    Version => "0.1", 
    Date => "",
    Authors => {{Name =>
    "", 
    Email
    =>
    "", 
    HomePage
    =>
    ""}},
    Headline
    =>
    "",
    DebuggingMode
    =>
    true
    )

export
{}

--

beginDocumentation()

  doc
  ///
  Key
  NCF
  Headline
  Description
  Text
  Example
  Caveat
  SeeAlso
  ///

  doc
  ///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Consequences
  Description
  Text
  Example
  Code
  Pre
  Caveat
  SeeAlso
  ///

  TEST
  ///
  --
  test
  code
  and
  assertions
  here
  --
  may
  have
  as
  many
  TEST
  sections
  as
  needed
  ///




end

--

restart 
loadPackage "NCF"

2+2

