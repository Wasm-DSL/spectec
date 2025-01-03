Types
-----

Simple :ref:`types <syntax-type>`, such as :ref:`number types <syntax-numtype>` are universally valid.
However, restrictions apply to most other types, such as :ref:`reference types <syntax-reftype>`, :ref:`function types <syntax-functype>`, as well as the :ref:`limits <syntax-limits>` of :ref:`table types <syntax-tabletype>` and :ref:`memory types <syntax-memtype>`, which must be checked during validation.

Moreover, :ref:`block types <syntax-blocktype>` are converted to plain :ref:`function types <syntax-functype>` for ease of processing.


.. index:: number type
   pair: validation; number type
   single: abstract syntax; number type
.. _valid-numtype:

Number Types
~~~~~~~~~~~~
$${rule-prose: Numtype_ok}
.. todo::
 below is the official specification

:ref:`Number types <syntax-numtype>` are always valid.

$${rule: Numtype_ok}


.. index:: vector type
   pair: validation; vector type
   single: abstract syntax; vector type
.. _valid-vectype:

Vector Types
~~~~~~~~~~~~
$${rule-prose: Vectype_ok}
.. todo::
 below is the official specification

:ref:`Vector types <syntax-vectype>` are always valid.

$${rule: Vectype_ok}


.. index:: heap type, type identifier
   pair: validation; heap type
   single: abstract syntax; heap type
.. _valid-heaptype:

Heap Types
~~~~~~~~~~
Concrete :ref:`heap types <syntax-heaptype>` are only valid when the :ref:`type index <syntax-typeidx>` is,
while abstract ones are vacuously valid.


:math:`\absheaptype`
....................
$${rule-prose: Heaptype_ok/abs}
.. todo::
 below is the official specification

* The heap type is valid.

$${rule: Heaptype_ok/abs}


:math:`\typeidx`
................
$${rule-prose: Heaptype_ok/typeidx}
.. todo::
 below is the official specification

* The type :math:`C.\CTYPES[\typeidx]` must be defined in the context.

* Then the heap type is valid.

$${rule: Heaptype_ok/typeidx}


.. index:: reference type, heap type
   pair: validation; reference type
   single: abstract syntax; reference type
.. _valid-reftype:

Reference Types
~~~~~~~~~~~~~~~
$${rule-prose: Reftype_ok}
.. todo::
 below is the official specification

:ref:`Reference types <syntax-reftype>` are valid when the referenced :ref:`heap type <syntax-heaptype>` is.

:math:`\REF~\NULL^?~\heaptype`
..............................

* The heap type :math:`\heaptype` must be :ref:`valid <valid-heaptype>`.

* Then the reference type is valid.

$${rule: Reftype_ok}


.. index:: value type, reference type, number type, vector type
   pair: validation; value type
   single: abstract syntax; value type
.. _valid-valtype:

Value Types
~~~~~~~~~~~
$${rule-prose: Valtype_ok}
.. todo::
 below is the official specification

Valid :ref:`value types <syntax-valtype>` are either valid :ref:`number types <valid-numtype>`, valid :ref:`vector types <valid-vectype>`, or valid :ref:`reference types <valid-reftype>`.


.. index:: block type, instruction type
   pair: validation; block type
   single: abstract syntax; block type
.. _valid-blocktype:

Block Types
~~~~~~~~~~~

:ref:`Block types <syntax-blocktype>` may be expressed in one of two forms, both of which are converted to :ref:`instruction types <syntax-instrtype>` by the following rules.

:math:`\typeidx`
................
$${rule-prose: Blocktype_ok/typeidx}
.. todo::
 below is the official specification

* The type :math:`C.\CTYPES[\typeidx]` must be defined in the context.

* The :ref:`expansion <aux-expand-deftype>` of :math:`C.\CFUNCS[\typeidx]` must be a :ref:`function type <syntax-functype>` :math:`\TFUNC~[t_1^\ast] \toF [t_2^\ast]`.

* Then the block type is valid as :ref:`instruction type <syntax-instrtype>` :math:`[t_1^\ast] \to [t_2^\ast]`.

$${rule: Blocktype_ok/typeidx}


:math:`[\valtype^?]`
....................
$${rule-prose: Blocktype_ok/valtype}
.. todo::
 below is the official specification

* The value type :math:`\valtype` must either be absent, or :ref:`valid <valid-valtype>`.

* Then the block type is valid as :ref:`instruction type <syntax-instrtype>` :math:`[] \to [\valtype^?]`.

$${rule: Blocktype_ok/valtype}


.. index:: result type, value type
   pair: validation; result type
   single: abstract syntax; result type
.. _valid-resulttype:

Result Types
~~~~~~~~~~~~

:math:`[t^\ast]`
................
$${rule-prose: Resulttype_ok}
.. todo::
 below is the official specification

* Each :ref:`value type <syntax-valtype>` :math:`t_i` in the type sequence :math:`t^\ast` must be :ref:`valid <valid-valtype>`.

* Then the result type is valid.

$${rule: Resulttype_ok}


.. index:: instruction type
   pair: validation; instruction type
   single: abstract syntax; instruction type
.. _valid-instrtype:

Instruction Types
~~~~~~~~~~~~~~~~~
$${rule-prose: Instrtype_ok}
.. todo::
 below is the official specification

:math:`[t_1^\ast] \rightarrow_{x^\ast} [t_2^\ast]`
..................................................

* The :ref:`result type <syntax-resulttype>` :math:`[t_1^\ast]` must be :ref:`valid <valid-resulttype>`.

* The :ref:`result type <syntax-resulttype>` :math:`[t_2^\ast]` must be :ref:`valid <valid-resulttype>`.

* Each :ref:`local index <syntax-localidx>` :math:`x_i` in :math:`x^\ast` must be defined in the context.

* Then the instruction type is valid.

$${rule: Instrtype_ok}


.. index:: function type
   pair: validation; function type
   single: abstract syntax; function type
.. _valid-functype:

Function Types
~~~~~~~~~~~~~~

:math:`[t_1^\ast] \toF [t_2^\ast]`
..................................
$${rule-prose: Functype_ok}
.. todo::
 below is the official specification

* The :ref:`result type <syntax-resulttype>` :math:`[t_1^\ast]` must be :ref:`valid <valid-resulttype>`.

* The :ref:`result type <syntax-resulttype>` :math:`[t_2^\ast]` must be :ref:`valid <valid-resulttype>`.

* Then the function type is valid.

$${rule: Functype_ok}


.. index:: composite type, function type, aggregate type, structure type, array type, field type
   pair: validation; composite type
   pair: validation; aggregate type
   pair: validation; structure type
   pair: validation; array type
   single: abstract syntax; composite type
   single: abstract syntax; function type
   single: abstract syntax; structure type
   single: abstract syntax; array type
   single: abstract syntax; field type
.. _valid-comptype:
.. _valid-aggrtype:
.. _valid-structtype:
.. _valid-arraytype:

Composite Types
~~~~~~~~~~~~~~~

:math:`\TFUNC~\functype`
........................
$${rule-prose: Comptype_ok/func}
.. todo::
 below is the official specification

* The :ref:`function type <syntax-functype>` :math:`\functype` must be :ref:`valid <valid-functype>`.

* Then the composite type is valid.

$${rule: Comptype_ok/func}

:math:`\TSTRUCT~\fieldtype^\ast`
................................
$${rule-prose: Comptype_ok/struct}
.. todo::
 below is the official specification

* For each :ref:`field type <syntax-fieldtype>` :math:`\fieldtype_i` in :math:`\fieldtype^\ast`:

  * The :ref:`field type <syntax-fieldtype>` :math:`\fieldtype_i` must be :ref:`valid <valid-fieldtype>`.

* Then the composite type is valid.

$${rule: Comptype_ok/struct}

:math:`\TARRAY~\fieldtype`
..........................
$${rule-prose: Comptype_ok/array}
.. todo::
 below is the official specification

* The :ref:`field type <syntax-fieldtype>` :math:`\fieldtype` must be :ref:`valid <valid-fieldtype>`.

* Then the composite type is valid.

$${rule: Comptype_ok/array}


.. index:: field type, storage type, packed type, value type, mutability
   pair: validation; field type
   pair: validation; storage type
   pair: validation; packed type
   single: abstract syntax; field type
   single: abstract syntax; storage type
   single: abstract syntax; packed type
   single: abstract syntax; value type
.. _valid-fieldtype:
.. _valid-storagetype:
.. _valid-packtype:

Field Types
~~~~~~~~~~~

:math:`\mut~\storagetype`
.........................
$${rule-prose: Fieldtype_ok}
.. todo::
 below is the official specification

* The :ref:`storage type <syntax-storagetype>` :math:`\storagetype` must be :ref:`valid <valid-storagetype>`.

* Then the field type is valid.

$${rule: Fieldtype_ok}


:math:`\packtype`
.................
$${rule-prose: Packtype_ok}
.. todo::
 below is the official specification

* The packed type is valid.

$${rule: Packtype_ok}


.. index:: recursive type, sub type, composite type, final, subtyping
   pair: abstract syntax; recursive type
   pair: abstract syntax; sub type
.. _valid-rectype:
.. _valid-subtype:

Recursive Types
~~~~~~~~~~~~~~~

:ref:`Recursive types <syntax-rectype>` are validated for a specific :ref:`type index <syntax-typeidx>` that denotes the index of the type defined by the recursive group.

:math:`\TREC~\subtype^\ast`
...........................
$${rule-prose: Rectype_ok}
.. todo::
 below is the official specification

* Either the sequence :math:`\subtype^\ast` is empty.

* Or:

  * The first :ref:`sub type <syntax-subtype>` of the sequence :math:`\subtype^\ast` must be :ref:`valid <valid-subtype>` for the :ref:`type index <syntax-typeidx>` :math:`x`.

  * The remaining sequence :math:`\subtype^\ast` must be :ref:`valid <valid-rectype>` for the :ref:`type index <syntax-typeidx>` :math:`x + 1`.

* Then the recursive type is valid for the :ref:`type index <syntax-typeidx>` :math:`x`.

$${rule: {Rectype_ok/empty Rectype_ok/cons}}


:math:`\TSUB~\TFINAL^?~y^\ast~\comptype`
........................................
$${rule-prose: Subtype_ok}
.. todo::
 below is the official specification

* The :ref:`composite type <syntax-comptype>` :math:`\comptype` must be :ref:`valid <valid-comptype>`.

* The sequence :math:`y^\ast` may be no longer than :math:`1`.

* For every :ref:`type index <syntax-typeidx>` :math:`y_i` in :math:`y^\ast`:

  * The :ref:`type index <syntax-typeidx>` :math:`y_i` must be smaller than :math:`x`.

  * The :ref:`type index <syntax-typeidx>` :math:`y_i` must exist in the context :math:`C`.

  * Let :math:`\subtype_i` be the :ref:`unrolling <aux-unroll-deftype>` of the :ref:`defined type <syntax-deftype>` :math:`C.\CTYPES[y_i]`.

  * The :ref:`sub type <syntax-subtype>` :math:`\subtype_i` must not contain :math:`\TFINAL`.

  * Let :math:`\comptype'_i` be the :ref:`composite type <syntax-comptype>` in :math:`\subtype_i`.

  * The :ref:`composite type <syntax-comptype>` :math:`\comptype` must :ref:`match <match-comptype>` :math:`\comptype'_i`.

* Then the sub type is valid for the :ref:`type index <syntax-typeidx>` :math:`x`.

$${rule: Subtype_ok}

.. note::
   The side condition on the index ensures that a declared supertype is a previously defined types,
   preventing cyclic subtype hierarchies.

   Future versions of WebAssembly may allow more than one supertype.


.. index:: defined type, recursive type, unroll, expand
   pair: abstract syntax; defined type
.. _valid-deftype:

Defined Types
~~~~~~~~~~~~~

:math:`\rectype.i`
..................
$${rule-prose: Deftype_ok}
.. todo::
 below is the official specification

* The :ref:`recursive type <syntax-rectype>` :math:`\rectype` must be :ref:`valid <valid-rectype>` for some :ref:`type index <syntax-typeidx>` :math:`x`.

* Let :math:`\TREC~\subtype^\ast` be the :ref:`defined type <syntax-rectype>` :math:`\rectype`.

* The number :math:`i` must be smaller than the length of the sequence :math:`\subtype^\ast` of :ref:`sub types <syntax-subtype>`.

* Then the defined type is valid.

$${rule: Deftype_ok}


.. index:: limits
   pair: validation; limits
   single: abstract syntax; limits
.. _valid-limits:

Limits
~~~~~~

:ref:`Limits <syntax-limits>` must have meaningful bounds that are within a given range.

:math:`\{ \LMIN~n, \LMAX~m^? \}`
................................
$${rule-prose: Limits_ok}
.. todo::
 below is the official specification

* The value of :math:`n` must not be larger than :math:`k`.

* If the maximum :math:`m^?` is not empty, then:

  * Its value must not be larger than :math:`k`.

  * Its value must not be smaller than :math:`n`.

* Then the limit is valid within range :math:`k`.

$${rule: Limits_ok}


.. index:: table type, reference type, limits
   pair: validation; table type
   single: abstract syntax; table type
.. _valid-tabletype:

Table Types
~~~~~~~~~~~

:math:`\addrtype~\limits~\reftype`
..................................
$${rule-prose: Tabletype_ok}
.. todo::
 below is the official specification

* The limits :math:`\limits` must be :ref:`valid <valid-limits>` within range :math:`2^{|\addrtype|}-1`.

* The reference type :math:`\reftype` must be :ref:`valid <valid-reftype>`.

* Then the table type is valid.

$${rule: Tabletype_ok}


.. index:: memory type, limits
   pair: validation; memory type
   single: abstract syntax; memory type
.. _valid-memtype:

Memory Types
~~~~~~~~~~~~

:math:`\addrtype~\limits`
.........................
$${rule-prose: Memtype_ok}
.. todo::
 below is the official specification

* The limits :math:`\limits` must be :ref:`valid <valid-limits>` within range :math:`2^{|\addrtype|-16}`.

* Then the memory type is valid.

$${rule: Memtype_ok}


.. index:: tag type, function type, exception tag
   pair: validation; tag type
   single: abstract syntax; tag type
.. _valid-tagtype:

Tag Types
~~~~~~~~~

:math:`[t_1^n] \to [t_2^m]`
...........................
$${rule-prose: Tagtype_ok}
.. todo::
 below is the official specification

* The :ref:`function type <syntax-functype>` :math:`[t_1^n] \to [t_2^m]` must be :ref:`valid <valid-functype>`.

* The type sequence :math:`t_2^m` must be empty.

* Then the tag type is valid.

$${rule: Tagtype_ok}


.. index:: global type, value type, mutability
   pair: validation; global type
   single: abstract syntax; global type
.. _valid-globaltype:

Global Types
~~~~~~~~~~~~

:math:`\mut~\valtype`
.....................
$${rule-prose: Globaltype_ok}
.. todo::
 below is the official specification

* The value type :math:`\valtype` must be :ref:`valid <valid-valtype>`.

* Then the global type is valid.

$${rule: Globaltype_ok}


.. index:: external type, function type, table type, memory type, global type
   pair: validation; external type
   single: abstract syntax; external type
.. _valid-externtype:

External Types
~~~~~~~~~~~~~~

:math:`\XTFUNC~\deftype`
........................
$${rule-prose: Externtype_ok/func}
.. todo::
 below is the official specification

* The :ref:`defined type <syntax-deftype>` :math:`\deftype` must be :ref:`valid <valid-deftype>`.

* The :ref:`defined type <syntax-deftype>` :math:`\deftype` must be a :ref:`function type <syntax-functype>`.

* Then the external type is valid.

$${rule: Externtype_ok/func}


:math:`\XTTABLE~\tabletype`
...........................
$${rule-prose: Externtype_ok/table}
.. todo::
 below is the official specification

* The :ref:`table type <syntax-tabletype>` :math:`\tabletype` must be :ref:`valid <valid-tabletype>`.

* Then the external type is valid.

$${rule: Externtype_ok/table}


:math:`\XTMEM~\memtype`
.......................
$${rule-prose: Externtype_ok/mem}
.. todo::
 below is the official specification

* The :ref:`memory type <syntax-memtype>` :math:`\memtype` must be :ref:`valid <valid-memtype>`.

* Then the external type is valid.

$${rule: Externtype_ok/mem}


:math:`\XTTAG~\tagtype`
.......................
$${rule-prose: Externtype_ok/tag}
.. todo::
 below is the official specification

* The :ref:`tag type <syntax-tagtype>` :math:`\tagtype` must be :ref:`valid <valid-tagtype>`.

* Then the external type is valid.

$${rule: Externtype_ok/tag}


:math:`\XTGLOBAL~\globaltype`
.............................
$${rule-prose: Externtype_ok/global}
.. todo::
 below is the official specification

* The :ref:`global type <syntax-globaltype>` :math:`\globaltype` must be :ref:`valid <valid-globaltype>`.

* Then the external type is valid.

$${rule: Externtype_ok/global}

Defaultable Types
~~~~~~~~~~~~~~~~~

A type is *defaultable* if it has a :ref:`default value <default-val>` for initialization.

Value Types
...........

$${rule-prose: Defaultable}
.. todo::
 below is the official specification

* A defaultable :ref:`value type <syntax-valtype>` :math:`t` must be:

  - either a :ref:`number type <syntax-numtype>`,

  - or a :ref:`vector type <syntax-vectype>`,

  - or a :ref:`nullable reference type <syntax-numtype>`.

$${rule: Defaultable}
