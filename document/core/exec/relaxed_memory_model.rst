.. index:: ! relaxed memory model

Relaxed Memory Model
~~~~~~~~~~~~~~~~~~~~~~

The execution of a WebAssembly program gives rise to a trace of events. WebAssembly’s relaxed memory model constrains the observable behaviours of the program’s execution by defining a consistency condition on the trace of events.

.. _op-time:
.. _op-timep:
.. _op-locationf:
.. _op-ordf:
.. _op-overlap:
.. _op-same:
.. _op-reading:
.. _op-writing:
.. _op-susp:
.. _op-read:
.. _op-write:
.. _op-offset:
.. _op-sync:
.. _op-range:
.. _op-tearfree:
.. _op-id:
.. _op-func-lower:
.. _syntax-event:
.. _syntax-trace:
.. _syntax-action:
.. _syntax-int:

.. math::
   \begin{array}{lll@{\qquad}l}
   \time(act*\ at\ \timestamp_{p}\ \timestamp) &=& \timestamp \\
   \timep(act*\ at\ \timestamp_{p}\ \timestamp) &=& \timestamp \\ 

   \locationf(rd\ \ord\ \location\ \storeval) &=& \location \\
   \locationf(wr\ \ord\ \location\ \storeval) &=& \location \\
   \locationf(rmw\ \location\ \storeval) &=& \location \\
   \locationf(wait\ \location\ \s64) &=& \location \\
   \locationf(woken\ \ord\ \location\ \storeval) &=& \location \\
   \locationf(timeout\ \location) &=& \location \\
   \locationf(notify\ \location\ \u32 \u32) &=& \location \\ 

   \ordf(rd\ \ord\ \location\ \storeval) &=& \ord \\
   \ordf(wr\ \ord\ \location\ \storeval) &=& \ord \\
   \ordf(rmw\ \location\ \storeval) &=& \SEQCST \\

   \overlap(\action_{1}, \action_{2}) &=& (range(\action_{1}) \cup range(action_{2}) \neq \epsilon) \\
   \same(\action_{1}, \action_{2}) &=& (range(\action_{1}) = range(action_{2}))

   \reading(\action) &=& (read(\action) \neq \epsilon) \\
   \writing(\action) &=& (write(\action) \neq \epsilon) \\

   \susp(\u32,\ wait\ \region[\u32]\ \s64) &=& wait\ \region[u32]\\
   \susp(\u32,\ woken\ \region[\u32]) &=& woken\ \region[u32]\\
   \susp(\u32,\ timeout\ \region[\u32]) &=& timeout\ \region[u32]\\
   \susp(\u32,\ notify\ \region[\u32]\ \u32'\ \u32'') &=& notify\ \region[u32]\ \u32'\ \u32''\\
   \susp(\u32,\ \action) &=& eps\\

   \read(\action) &=& (\byte*) \\
   \write(\action) &=& (\byte_{1}*) \\

   \offset(\action) &=& \u32\quad (if\ \locationf(\action)=\region[\u32]) \\

   \sync(\action_{1}, \action_{2}) &=& (\same(\action_{1}, \action_{2})\ \land \\
                           \qquad \qquad \qquad \qquad \qquad \qquad \ord(\action_{1}) = ord(\action_{2}) = \SEQCST) \\

   \range(\action) &=& [\u32...\u32+n-1] \\
                        (if\ \location(\action)=\region[\u32]\land\\
                        \qquad \qquad \qquad \qquad \qquad n = max(\|\read(\action)\|,\|\write(\action)\|)) \\

   \tearfree(rd_{\ord}\ \location\ \byte^{*}) &=& \bot (if\ \ord = \UNORD \vee\ \ord=\INIT) \\
   \tearfree(wr_{\ord}\ \location\ \byte^{*}) &=& \bot (if\ \ord = \UNORD \vee\ \ord=\INIT) \\
   \tearfree(\action) &=& \top (otherwise) \\

   \id(\action) &=& \action \\

   \funclower(\action) &=& \action \\

   \trace &=& \event* \\

   \end{array}

Consistency
~~~~~~~~~~~


:math:`Relaxed Memory Model`
.....................................

.. _relation-consistent:
.. _relation-consistent-with:
.. _relation-happens-before:
.. _relation-reads-each-from:
.. _relation-reads-from:
.. _relation-suspensions-consistent:
.. _relation-suspensions-consistent-with:
.. _relation-value-consistent:
.. _relation-hb-consistent:
.. _relation-sc-last-visible:
.. _relation-no-tear:
.. _op-reading-reg:
.. _op-overlap-reg:
.. _op-happens-before:
.. _op-tot:
.. _op-implies-tot-happens-before:
.. _op-implies:
.. _op-implies-consistent-with:
.. _op-not-in-range:
.. _op-write-filter:
.. _op-reading-filter:
.. _op-region-action-filter:
.. _op-forall:
.. _op-access-r:
.. _op-loc-in-region:
.. _op-same-and-tear-free-filter:
.. _op-tear-free:
.. _op-reading-action-filter:
.. _op-write-action-filter:
.. _op-susp-filter:
.. _op-init-filter:
.. _op-unfold-u32:
.. _op-unfold-nat:
.. _op-allreg:
.. _op-allnat:
.. _forall-implies-consistent-with:
.. _forall-implies-happens-tot-before:
.. _relation-for-all-consistent-with:
.. _relation-for-all-suspensions-consistent:
.. _relation-for-all-reads-from:
.. _relation-for-all-reads-each-from:

$${definition: readingfilter writefilter initfilter readingactionfilter writeactionfilter suspfilter}

$${rule: Consistent}

$${rule: Consistentwith}

$${rule: Readseachfrom}

$${rule: Readsfrom}

$${rule: Valueconsistent}

$${rule: Hbconsistent}

$${rule: Sclastvisible}

$${rule: Notear}

$${rule: Suspensionsconsistent}

$${rule: Suspensionsconsistentwith}
