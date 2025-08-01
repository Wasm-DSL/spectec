.. index:: ! binary format, module, byte, file extension, abstract syntax

Conventions
-----------

The binary format for WebAssembly :ref:`modules <module>` is a dense linear *encoding* of their :ref:`abstract syntax <syntax-module>`.
[#compression]_

The format is defined by an *attribute grammar* whose only terminal symbols are :ref:`bytes <syntax-byte>`.
A byte sequence is a well-formed encoding of a module if and only if it is generated by the grammar.

Each production of this grammar has exactly one synthesized attribute: the abstract syntax that the respective byte sequence encodes.
Thus, the attribute grammar implicitly defines a *decoding* function
(i.e., a parsing function for the binary format).

Except for a few exceptions, the binary grammar closely mirrors the grammar of the abstract syntax.

.. note::
   Some phrases of abstract syntax have multiple possible encodings in the binary format.
   For example, numbers may be encoded as if they had optional leading zeros.
   Implementations of decoders must support all possible alternatives;
   implementations of encoders can pick any allowed encoding.

The recommended extension for files containing WebAssembly modules in binary format is ":math:`\T{.wasm}`"
and the recommended |MediaType|_ is ":math:`\T{application/wasm}`".

.. [#compression]
   Additional encoding layers -- for example, introducing compression -- may be defined on top of the basic representation defined here.
   However, such layers are outside the scope of the current specification.


.. index:: grammar notation, notation, byte
   single: binary format; grammar
   pair: binary format; notation
.. _binary-grammar:

Grammar
~~~~~~~

The following conventions are adopted in defining grammar rules for the binary format.
They mirror the conventions used for :ref:`abstract syntax <grammar>`.
In order to distinguish symbols of the binary syntax from symbols of the abstract syntax, ${grammar-case: Btypewriter} font is adopted for the former.

* Terminal symbols are :ref:`bytes <syntax-byte>` expressed in hexadecimal notation: ${grammar-case: 0x0F}.

* Nonterminal symbols are written in typewriter font: ${grammar-case: Bvaltype}, ${grammar-case: Binstr}.

* ${grammar-case: $(B)^n} is a sequence of ${:n>=0} iterations of ${:B}.

* ${grammar-case: $(B)*} is a possibly empty sequence of iterations of ${:B}.
  (This is a shorthand for ${:B^n} used where ${:n} is not relevant.)

* ${grammar-case: $(B)?} is an optional occurrence of ${:B}.
  (This is a shorthand for ${:B^n} where ${:n<=1}.)

* ${grammar-case: x:$(B)} denotes the same language as the nonterminal ${:B}, but also binds the variable ${:x} to the attribute synthesized for ${:B}.
  A pattern may also be used instead of a variable, e.g., ${grammar-case: 7:$(B)}.

* Productions are written ${grammar: Bsym}, where each ${:A_i} is the attribute that is synthesized for ${grammar-case: Bsym} in the given case, usually from attribute variables bound in ${:B_i}.

* Large productions may be split into multiple definitions, indicated by ending the first one with explicit ellipses, :math:`\B{sym} ::= B_1 \Rightarrow A_1 ~|~ \dots`, and starting continuations with ellipses, :math:`\B{sym} ::= \dots ~|~ B_2 \Rightarrow A_2`.

* Some productions are augmented by side conditions in parentheses, which restrict the applicability of the production. They provide a shorthand for a combinatorial expansion of the production into many separate cases.

* If the same meta variable or non-terminal symbol appears multiple times in a production (in the syntax or in an attribute), then all those occurrences must have the same instantiation.
  (This is a shorthand for a side condition requiring multiple different variables to be equal.)

.. note::
   For example, the :ref:`binary grammar <binary-numtype>` for :ref:`number types <syntax-numtype>` is given as follows:

   $${grammar: Bnumtype}

   Consequently, the byte ${grammar-case: 0x7F} encodes the type ${numtype:I32},
   ${grammar-case: 0x7E} encodes the type ${numtype: I64}, and so forth.
   No other byte value is allowed as the encoding of a number type.

   The :ref:`binary grammar <binary-limits>` for :ref:`limits <syntax-limits>` is defined as follows:   

   $${grammar: Blimits_}

   That is, a limits pair is encoded as either the byte ${:0x00} followed by the encoding of a ${:u32} value,
   or the byte ${grammar-case: 0x01} followed by two such encodings. 
   The variables ${:n} and ${:m} name the attributes of the respective ${grammar-case: Bu32} nonterminals, which in this case are the actual :ref:`unsigned integers <syntax-uint>` those decode into.
   The attribute of the complete production then is the abstract syntax for the limit, expressed in terms of the former values.


.. _binary-notation:

Auxiliary Notation
~~~~~~~~~~~~~~~~~~

When dealing with binary encodings the following notation is also used:

* ${grammar-case: eps} denotes the empty byte sequence.

* ${:||B||} is the length of the byte sequence generated from the production ${grammar-case: B} in a derivation.


.. index:: list
   pair: binary format; list
.. _binary-list:

Lists
~~~~~

:ref:`Lists <syntax-list>` are encoded with their ${grammar-case:Bu32} length followed by the encoding of their element sequence.

$${grammar: Blist}
