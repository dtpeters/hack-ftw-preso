 ;;; Copyright (C) 2014 Ludovic Courtès <address@hidden>
 ;;;
 ;;; This library is free software; you can redistribute it and/or
 ;;; modify it under the terms of the GNU Lesser General Public
 ;;; License as published by the Free Software Foundation; either
 ;;; version 3 of the License, or (at your option) any later version.
 ;;;
 ;;; This library is distributed in the hope that it will be useful,
 ;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
 ;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 ;;; Lesser General Public License for more details.
 ;;;
 ;;; You should have received a copy of the GNU Lesser General Public
 ;;; License along with this library; if not, write to the Free Software
 ;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 
 USA
 
 (define-module (scm-pretty-printing)
   #:use-module (rnrs bytevectors)
   #:use-module (rnrs io ports)
   #:use-module (srfi srfi-1)
   #:use-module (srfi srfi-9)
   #:use-module (srfi srfi-9 gnu)
   #:use-module (srfi srfi-11)
   #:use-module (srfi srfi-26)
   #:use-module (srfi srfi-60)
   #:use-module (ice-9 match)
   #:use-module (ice-9 iconv)
   #:use-module (ice-9 format)
   #:use-module (ice-9 vlist)
   #:use-module (system foreign))
 
 ;;; Commentary:
 ;;;
 ;;; 'SCM' type tag decoding and more to support Guile debugging in GDB.
 ;;;
 ;;; Code:
 
 (define-syntax when-gdb
   (lambda (s)
     (let ((gdb? (false-if-exception (resolve-interface '(gdb)))))
       (syntax-case s ()
         ((_ body ...)
          (if gdb?
              #'(begin body ...)
              #'(begin)))))))
 
 (define-syntax if-gdb
   (lambda (s)
     (let ((gdb? (false-if-exception (resolve-interface '(gdb)))))
       (syntax-case s ()
         ((_ with-gdb without-gdb)
          (if gdb?
              #'with-gdb
              #'without-gdb))))))
 
 
 (when-gdb (use-modules ((gdb) #:hide (symbol?))
                        (gdb printing)))
 
 (define %word-size
   ;; The pointer size.
   (sizeof '*))
 
 
 ;;;
 ;;; Memory back-ends.
 ;;;
 
 (define-record-type <memory-backend>
   (memory-backend peek open)
   memory-backend?
   (peek memory-backend-peek)
   (open memory-backend-open))
 
 (when-gdb
  (define %gdb-memory-backend
    ;; The GDB back-end to access the inferior's memory.
    (let ((void* (type-pointer (lookup-type "void"))))
      (define (dereference-word address)
        ;; Return the word at ADDRESS.
        (value->integer
         (value-dereference (value-cast (make-value address)
                                        (type-pointer void*)))))
 
      (define (open address size)
        ;; Return a port to the SIZE bytes starting at ADDRESS.
        (if size
            (open-memory #:start address #:size size)
            (open-memory #:start address)))
 
      (memory-backend dereference-word open))))
 
 (define %ffi-memory-backend
   ;; The FFI back-end to access the current process's memory.  The main
   ;; purpose of this back-end is to allow testing.
   (let ()
     (define (dereference-word address)
       (let* ((ptr (make-pointer address))
              (bv  (pointer->bytevector ptr %word-size)))
         (bytevector-uint-ref bv 0 (native-endianness) %word-size)))
 
     (define (open address size)
       (define current-address address)
 
       (define (read-memory! bv index count)
         (let* ((ptr   (make-pointer current-address))
                (mem   (pointer->bytevector ptr count)))
           (bytevector-copy! mem 0 bv index count)
           (set! current-address (+ current-address count))
           count))
 
       (if size
           (let* ((ptr (make-pointer address))
                  (bv  (pointer->bytevector ptr size)))
             (open-bytevector-input-port bv))
           (let ((port (make-custom-binary-input-port "ffi-memory"
                                                      read-memory!
                                                      #f #f #f)))
             (setvbuf port _IONBF)
             port)))
 
     (memory-backend dereference-word open)))
 
 (define-inlinable (dereference-word backend address)
   "Return the word at ADDRESS, using BACKEND."
   (let ((peek (memory-backend-peek backend)))
     (peek address)))
 
 (define-syntax memory-port
   (syntax-rules ()
     "Return an input port to the SIZE bytes at ADDRESS, using BACKEND.  When
 SIZE is omitted, return an unbounded port to the memory at ADDRESS."
     ((_ backend address)
      (let ((open (memory-backend-open backend)))
        (open address #f)))
     ((_ backend address size)
      (let ((open (memory-backend-open backend)))
        (open address size)))))
 
 (define (get-word port)
   "Read a word from PORT and return it as an integer."
   (let ((bv (get-bytevector-n port %word-size)))
     (bytevector-uint-ref bv 0 (native-endianness) %word-size)))
 
 
 ;;;
 ;;; Matching bit patterns and cells.
 ;;;
 
 (define-syntax match-cell-words
   (syntax-rules (bytevector)
     ((_ port ((bytevector name len) rest ...) body)
      (let ((name      (get-bytevector-n port len))
            (remainder (modulo len %word-size)))
        (unless (zero? remainder)
          (get-bytevector-n port (- %word-size remainder)))
        (match-cell-words port (rest ...) body)))
     ((_ port (name rest ...) body)
      (let ((name (get-word port)))
        (match-cell-words port (rest ...) body)))
     ((_ port () body)
      body)))
 
 (define-syntax match-bit-pattern
   (syntax-rules (& || = _)
     ((match-bit-pattern bits ((a || b) & n = c) consequent alternate)
      (let ((tag (logand bits n)))
        (if (= tag c)
            (let ((b tag)
                  (a (logand bits (bitwise-not n))))
              consequent)
            alternate)))
     ((match-bit-pattern bits (x & n = c) consequent alternate)
      (let ((tag (logand bits n)))
        (if (= tag c)
            (let ((x bits))
              consequent)
            alternate)))
     ((match-bit-pattern bits (_ & n = c) consequent alternate)
      (let ((tag (logand bits n)))
        (if (= tag c)
            consequent
            alternate)))
     ((match-bit-pattern bits ((a << n) || c) consequent alternate)
      (let ((tag (bitwise-and bits (- (expt 2 n) 1))))
        (if (= tag c)
            (let ((a (arithmetic-shift bits (- n))))
              consequent)
            alternate)))))
 
 (define-syntax match-cell-clauses
   (syntax-rules ()
     ((_ port tag (((tag-pattern thing ...) body) rest ...))
      (match-bit-pattern tag tag-pattern
                         (match-cell-words port (thing ...) body)
                         (match-cell-clauses port tag (rest ...))))
     ((_ port tag ())
      (inferior-object 'unmatched-tag tag))))
 
 (define-syntax match-cell
   (syntax-rules ()
     "Match a cell---i.e., a non-immediate value other than a pair.  The
 cell's contents are read from PORT."
     ((_ port (pattern body ...) ...)
      (let ((port* port)
            (tag   (get-word port)))
        (match-cell-clauses port* tag
                            ((pattern (begin body ...))
                             ...))))))
 
 (define-syntax match-scm-clauses
   (syntax-rules ()
     ((_ bits
         (bit-pattern body ...)
         rest ...)
      (match-bit-pattern bits bit-pattern
                         (begin body ...)
                         (match-scm-clauses bits rest ...)))
     ((_ bits)
      'unmatched-scm)))
 
 (define-syntax match-scm
   (syntax-rules ()
     "Match BITS, an integer representation of an 'SCM' value, against
 CLAUSES.  Each clause must have the form:
 
   (PATTERN BODY ...)
 
 PATTERN is a bit pattern that may specify bitwise operations on BITS to
 determine if it matches.  TEMPLATE specify the name of the variable to bind
 the matching bits, possibly with bitwise operations to extract it from BITS."
     ((_ bits clauses ...)
      (let ((bits* bits))
        (match-scm-clauses bits* clauses ...)))))
 
 
 ;;;
 ;;; Tags.
 ;;;
 
 ;; Immediate values.
 (define %tc2-int 2)
 (define %tc3-imm24 4)
 
 (define %tc3-cons 0)
 (define %tc3-int1 %tc2-int)
 (define %tc3-int2 (+ %tc2-int 4))
 
 (define %tc8-char (+ 8 %tc3-imm24))
 (define %tc8-flag (+ %tc3-imm24 0))
 
 ;; Cell types.
 (define %tc3-struct 1)
 (define %tc7-symbol 5)
 (define %tc7-vector 13)
 (define %tc7-string 21)
 (define %tc7-number 23)
 (define %tc7-hashtable 29)
 (define %tc7-pointer 31)
 (define %tc7-fluid 37)
 (define %tc7-stringbuf 39)
 (define %tc7-dynamic-state 45)
 (define %tc7-frame 47)
 (define %tc7-objcode 53)
 (define %tc7-vm 55)
 (define %tc7-vm-continuation 71)
 (define %tc7-bytevector 77)
 (define %tc7-program 79)
 (define %tc7-port 125)
 (define %tc7-smob 127)
 
 (define %tc16-bignum (+ %tc7-number (* 1 256)))
 (define %tc16-real (+ %tc7-number (* 2 256)))
 (define %tc16-complex (+ %tc7-number (* 3 256)))
 (define %tc16-fraction (+ %tc7-number (* 4 256)))
 
 
 ;; "Stringbufs".
 (define-record-type <stringbuf>
   (stringbuf string)
   stringbuf?
   (string stringbuf-contents))
 
 (set-record-type-printer! <stringbuf>
                           (lambda (stringbuf port)
                             (display "#<stringbuf " port)
                             (write (stringbuf-contents stringbuf) port)
                             (display "#>" port)))
 
 ;; Structs.
 (define-record-type <inferior-struct>
   (inferior-struct name fields)
   inferior-struct?
   (name   inferior-struct-name)
   (fields inferior-struct-fields))
 
 (set-record-type-printer! <inferior-struct>
                           (lambda (struct port)
                             (format port "#<struct ~a"
                                     (inferior-struct-name struct))
                             (for-each (lambda (field)
                                         (format port " ~s" field))
                                       (inferior-struct-fields struct))
                             (format port "~x>" (object-address struct))))
 
 ;; Fluids.
 (define-record-type <inferior-fluid>
   (inferior-fluid number value)
   inferior-fluid?
   (number inferior-fluid-number)
   (value  inferior-fluid-value))
 
 (set-record-type-printer! <inferior-fluid>
                           (lambda (fluid port)
                             (match fluid
                               (($ <inferior-fluid> number)
                                (format port "#<fluid ~a ~x>"
                                        number
                                        (object-address fluid))))))
 
 ;; Object type to represent complex objects from the inferior process that
 ;; cannot be really converted to usable Scheme objects in the current
 ;; process.
 (define-record-type <inferior-object>
   (%inferior-object kind sub-kind address)
   inferior-object?
   (kind     inferior-object-kind)
   (sub-kind inferior-object-sub-kind)
   (address  inferior-object-address))
 
 (define inferior-object
   (case-lambda
     "Return an object representing an inferior object at ADDRESS, of type
 KIND/SUB-KIND."
     ((kind address)
      (%inferior-object kind #f address))
     ((kind sub-kind address)
      (%inferior-object kind sub-kind address))))
 
 (set-record-type-printer! <inferior-object>
                           (lambda (io port)
                             (match io
                               (($ <inferior-object> kind sub-kind address)
                                (format port "#<~a ~:[~*~;~a ~]~x>"
                                        kind sub-kind sub-kind
                                        address)))))
 
 
 (define (type-name-from-descriptor descriptor-array type-number)
   "Return the name of the type TYPE-NUMBER as seen in DESCRIPTOR-ARRAY, or #f
 if the information is not available."
   (if-gdb
    (let ((descriptors (lookup-global-symbol descriptor-array)))
      (and descriptors
           (let ((code (type-code (symbol-type descriptors))))
             (or (= TYPE_CODE_ARRAY code)
                 (= TYPE_CODE_PTR code)))
           (let* ((type-descr (value-subscript (symbol-value descriptors)
                                               type-number))
                  (name       (value-field type-descr "name")))
             (value->string name))))
    #f))
 
 (define (inferior-smob type-number address)
   "Return an object representing the SMOB at ADDRESS whose type is
 TYPE-NUMBER."
   (inferior-object 'smob
                    (or (type-name-from-descriptor "scm_smobs" type-number)
                        type-number)
                    address))
 
 (define (inferior-port type-number address)
   "Return an object representing the port at ADDRESS whose type is
 TYPE-NUMBER."
   (inferior-object 'port
                    (or (type-name-from-descriptor "scm_ptobs" type-number)
                        type-number)
                    address))
 
 
 (define (address->inferior-struct address vtable-data-address backend)
   "Read the struct at ADDRESS using BACKEND.  Return an 'inferior-struct'
 object representing it."
   (define %vtable-layout-index 0)
   (define %vtable-name-index 5)
 
   (let* ((layout-address (+ vtable-data-address
                             (* %vtable-layout-index %word-size)))
          (layout-bits    (dereference-word backend layout-address))
          (layout         (scm->object layout-bits backend))
          (name-address   (+ vtable-data-address
                             (* %vtable-name-index %word-size)))
          (name-bits      (dereference-word backend name-address))
          (name           (scm->object name-bits backend)))
     (if ((@ (guile) symbol?) layout)
         (let* ((layout (symbol->string layout))
                (len    (/ (string-length layout) 2))
                (slots  (dereference-word backend (+ address %word-size)))
                (port   (memory-port backend slots (* len %word-size)))
                (fields (get-bytevector-n port (* len %word-size))))
           (inferior-struct name
                            (map (cut scm->object <> backend)
                                 (bytevector->uint-list fields
                                                        (native-endianness)
                                                        %word-size))))
         (inferior-object 'invalid-struct address))))
 
 (define %visited-cells
   ;; Vhash of already visited cells.  Used to detect cycles, typically in
   ;; structs.
   (make-parameter vlist-null))
 
 (define* (cell->object address #:optional (backend %ffi-memory-backend))
   "Return an object representing the object at ADDRESS, reading from memory
 using BACKEND."
   (if (vhash-assv address (%visited-cells))
       (inferior-object 'cycle address)
       (let ((port (memory-port backend address)))
         (match-cell port
           (((vtable-data-address & 7 = %tc3-struct))
            (parameterize ((%visited-cells (vhash-consv address #t
                                                        (%visited-cells))))
              (address->inferior-struct address
                                        (- vtable-data-address %tc3-struct)
                                        backend)))
           (((_ & #x7f = %tc7-symbol) buf hash props)
            (match (cell->object buf backend)
              (($ <stringbuf> string)
               (string->symbol string))))
           (((_ & #x7f = %tc7-string) buf start len)
            (match (cell->object buf backend)
              (($ <stringbuf> string)
               (substring string start (+ start len)))))
           (((_ & #x047f = %tc7-stringbuf) len (bytevector buf len))
            (stringbuf (bytevector->string buf "ISO-8859-1")))
           (((_ & #x047f = (bitwise-ior #x400 %tc7-stringbuf))
             len (bytevector buf (* 4 len)))
            (stringbuf (bytevector->string buf "UTF-32LE")))
           (((_ & #x7f = %tc7-bytevector) len address)
            (let ((bv-port (memory-port backend address len)))
              (get-bytevector-all bv-port)))
           ((((len << 7) || %tc7-vector) weakv-data)
            (let* ((len   (arithmetic-shift len -1))
                   (words (get-bytevector-n port (* len %word-size))))
              (list->vector
               (map (cut scm->object <> backend)
                    (bytevector->uint-list words (native-endianness)
                                           %word-size)))))
           ((((n << 8) || %tc7-fluid) init-value)
            (inferior-fluid n #f))                    ; TODO: show current 
 value
           (((_ & #x7f = %tc7-dynamic-state))
            (inferior-object 'dynamic-state address))
           ((((flags+type << 8) || %tc7-port))
            (inferior-port (logand flags+type #xff) address))
           (((_ & #x7f = %tc7-program))
            (inferior-object 'program address))
           (((_ & #xffff = %tc16-bignum))
            (inferior-object 'bignum address))
           (((_ & #xffff = %tc16-real) pad)
            (let* ((address (+ address (* 2 %word-size)))
                   (port    (memory-port backend address (sizeof double)))
                   (words   (get-bytevector-n port (sizeof double))))
              (bytevector-ieee-double-ref words 0 (native-endianness))))
           (((_ & #x7f = %tc7-number) mpi)
            (inferior-object 'number address))
           (((_ & #x7f = %tc7-hashtable))
            (inferior-object 'hash-table address))
           (((_ & #x7f = %tc7-pointer) address)
            (make-pointer address))
           (((_ & #x7f = %tc7-objcode))
            (inferior-object 'objcode address))
           (((_ & #x7f = %tc7-vm))
            (inferior-object 'vm address))
           (((_ & #x7f = %tc7-vm-continuation))
            (inferior-object 'vm-continuation address))
           ((((smob-type << 8) || %tc7-smob) word1)
            (inferior-smob smob-type address))))))
 
 
 (define* (scm->object bits #:optional (backend %ffi-memory-backend))
   "Return the Scheme object corresponding to BITS, the bits of an 'SCM'
 object."
   (match-scm bits
     (((integer << 2) || %tc2-int)
      integer)
     ((address & 6 = %tc3-cons)
      (let* ((type  (dereference-word backend address))
             (pair? (not (bit-set? 0 type))))
        (if pair?
            (let ((car    type)
                  (cdrloc (+ address %word-size)))
              (cons (scm->object car backend)
                    (scm->object (dereference-word backend cdrloc) backend)))
            (cell->object address backend))))
     (((char << 8) || %tc8-char)
      (integer->char char))
     (((flag << 8) || %tc8-flag)
      (case flag
        ((0)  #f)
        ((1)  #nil)
        ((3)  '())
        ((4)  #t)
        ((8)  (if #f #f))
        ((9)  (inferior-object 'undefined bits))
        ((10) (eof-object))
        ((11) (inferior-object 'unbound bits))))))
 
 
 ;;;
 ;;; GDB pretty-printer registration.
 ;;;
 
 (when-gdb
  (define scm-value->string
    ;; (compose object->string scm->object value->integer)
    (lambda* (v #:optional (backend %gdb-memory-backend))
      "Return a representation of value V as a string."
      (object->string (scm->object (value->integer v) backend))))
 
 
  (define %scm-pretty-printer
    (make-pretty-printer "SCM"
                         (lambda (pp value)
                           (let ((name (type-name (value-type value))))
                             (and (and name (string=? name "SCM"))
                                  (make-pretty-printer-worker
                                   #f              ; display hint
                                   (lambda (printer)
                                     (scm-value->string value 
 %gdb-memory-backend))
                                   #f))))))
 
  (define* (register-pretty-printer #:optional objfile)
    (prepend-pretty-printer! objfile %scm-pretty-printer))
 
  (define (libguile-objfile)
    (find (lambda (objfile)
            (string-contains (objfile-filename objfile) "libguile-2.0.so"))
          (objfiles)))
 
  (register-pretty-printer))
 
 
 ;;;
 ;;; VM stack walking.
 ;;;
 
 (when-gdb
  (export vm-stack-pointer vm-frame-pointer display-vm-frames)
 
  (define (find-vm-engine-frame)
    "Return the bottom-most frame containing a call to the VM engine."
    (define (vm-engine-frame? frame)
      (let ((sym (frame-function frame)))
        (and sym
             (member (symbol-name sym)
                     '("vm_debug_engine" "vm_regular_engine")))))
 
    (let loop ((frame (newest-frame)))
      (and frame
           (if (vm-engine-frame? frame)
               frame
               (loop (frame-older frame))))))
 
  (define (vm-stack-pointer)
    "Return the current value of the VM stack pointer or #f."
    (let ((frame (find-vm-engine-frame)))
      (and frame
           (frame-read-var frame "sp"))))
 
  (define (vm-frame-pointer)
    "Return the current value of the VM frame pointer or #f."
    (let ((frame (find-vm-engine-frame)))
      (and frame
           (frame-read-var frame "fp"))))
 
  (define* (display-vm-frames port)
    "Display the VM frames on PORT."
    (define (display-objects start end)
      (let loop ((number  0)
                 (address start))
        (when (and (> start 0) (<= address end))
          (let ((object (dereference-word %gdb-memory-backend address)))
            (format port "  slot ~a -> ~s~%"
                    number (scm->object object %gdb-memory-backend)))
          (loop (+ 1 number) (+ address %word-size)))))
 
    (let loop ((number 0)
               (sp     (value->integer (vm-stack-pointer)))
               (fp     (value->integer (vm-frame-pointer))))
      (unless (zero? fp)
        (let-values (((ra mvra link proc)
                      (vm-frame fp %gdb-memory-backend)))
          (format port "#~a ~s~%" number (scm->object proc 
 %gdb-memory-backend))
          (display-objects fp sp)
          (loop (+ 1 number) (- fp (* 5 %word-size)) link))))))
 
 ;; See libguile/frames.h.
 (define* (vm-frame fp #:optional (backend %ffi-memory-backend))
   "Return the components of the stack frame at FP."
   (let ((caller (dereference-word backend (- fp %word-size)))
         (ra     (dereference-word backend (- fp (* 2 %word-size))))
         (mvra   (dereference-word backend (- fp (* 3 %word-size))))
         (link   (dereference-word backend (- fp (* 4 %word-size)))))
     (values ra mvra link caller)))
 
 ;;; Local Variables:
 ;;; eval: (put 'match-scm 'scheme-indent-function 1)
 ;;; eval: (put 'match-cell 'scheme-indent-function 1)
 ;;; End:
 
 ;;; scmpp.scm ends here
