;; In a nutshell, this package implements functionality similar to the
;; `direnv' program (<https://direnv.net>), but it is written purely
;; in Emacs Lisp and does not require the actual `direnv' program to
;; be installed. It makes use of the dir-locals mechanism built-in to
;; Emacs to enable variables that are set for all files in a
;; subdirectory tree, and these variables can be exported to any
;; process launched by Emacs.
;;
;; A directory class 'provides-shell-env is defined which can be set
;; by calling `dir-local-env-enable' while within a `dired' buffer to
;; mark that directory as having it's own execution environment.

(require 'f)
(require 'avl-tree)

;; -------------------------------------------------------------------------------------------------
;; Buffer-local variables

(unintern 'disable-dir-local-env nil)

(defvar-local disable-dir-local-env nil
  "This variable automatically becomes buffer-local when set, and
is set to `nil' by default. When set to non-nil, the
`dir-local-env-get' function will always return `nil',
effectively disabling any variables set by
`dir-local-env-get'. This provides an easy way to temporarily
disable the `dir-local-env-get' mechanism for a buffer, if it is
behaving incorrectly due to misconfigured `dir-local-env'
variables.")

(defsubst dir-local-env-minor-mode (&optional enable)
  "The `dir-local-env-minor-mode' works on all buffers for which
the `default-directory' has been registered with
`dir-local-env-register' or is the child directory of a
registered directory, which may apply to a huge number of files
and buffers. It is possible to enable or disable the
`dir-local-env-minor-mode' on a per-buffer basis. This can be
used, for example, when you have a Magit buffer that needs to
access a local Git executable but your `dir-local-env' has set an
`exec-path' that does not have access to Git, which breaks
Magit. Use this function or `toggle-dir-local-env-minor-mode' in
the Magit buffer to restore the global `exec-path' which does
allow access to Git executables."
  (setq disable-dir-local-env (not (and enable (or (symbolp enable) (> enable 0))))))

(defun toggle-dir-local-env-minor-mode ()
  "Toggle whether or not the `disable-dir-local-env' variable is
set in the current buffer."
  (interactive)
  (setq-local disable-dir-local-env (not disable-dir-local-env))
  (message
   (format
    "dir-local-env %s in buffer %S"
    (if disable-dir-local-env "DISABLED" "ENABLED")
    (buffer-name))))

;; -------------------------------------------------------------------------------------------------
;; An implementation of a lightweight Trie data structure

(cl-defstruct
    (dlenv-registered-
     (:type vector))
"Data of this type indicate a function that has been registered
into the `dir-local-env-all-configs' or some other Trie that has
been built by the `dlenv-trie-' functions, and is constructed as
a result of a call to the `dlenv-trie--lookup-nearest' function
or (indirectly) to the `dlenv--project-dir-node' function.

The slots include:

- `node-env' Contains the actual environment dictionary for a
  directory.

- `proj-dir' The part of the query path that is registered,
  i.e. the project directory.

- `file-path' The part of the query path this is not registered,
   i.e. the path to the file relative to the project directory."
  (node-env nil :read-only t)
  (proj-dir nil :read-only t)
  (file-path nil :read-only t))


(cl-defstruct
    (dlenv-trie-node-
     (:type vector))
"This is the NODE that defines the structure the Trie that is
used to model the filesystem and directory-local environment
configurations. Recall that a Trie is a tree-like data structure
where every node may contain a leaf and branches to other Trie
nodes. The branches of each node contain a list of key-value
relations, where each KEY is an element of a sequence called a
\"path\". Therefore, the Trie acts as a store for path-value
relations, where each path SEGMENT is a key used to lookup the
individual key-value relation stored in the BRANCHES of each
NODE. An `avl-tree' is used to store branches, but the `avl-tree'
does not store key-value relations, it only stores nodes in a
tree according to some partial-ordernig function on the NODEs,
however it is possible to make the `avl-tree' into a key-value
store where each value is a NODE and by defining each NODE such
that it contains a key (which is the path SEGMENT) and defining
the partial ordering for the nodes as an ordering on these
keys (SEGMENTs)."
  (segment nil)
  (leaf nil)
  (branches nil))


(defun dlenv-trie-node--ordering (a b)
  "This is the partial ordering function for `dlenv-trie-node-'
values used by the `avl-tree' data structure for efficiently
storing nodes."
  (string-lessp (dlenv-trie-node--segment a) (dlenv-trie-node--segment b)))


(defsubst dlenv-trie--null (node)
"Return `t' if the given Trie NODE is `nil', or if all components
except for the SEGMENT key are `nil'."
  (or (null node)
      (and (null (dlenv-trie-node--branches node))
           (null (dlenv-trie-node--leaf node)))))

(defsubst dlenv-trie-node--assert-segment (node key k)
  "Checks that the `:segment' of the node is non-`nil' or else
signals an error."
  (when (null (dlenv-trie-node--segment node))
    (error "null path segment" :after k :of-key key :node node)))

(defsubst dlenv-trie--new-branches ()
  "Create an empty subtree (avl-tree) to be used as the second
component of a Trie node."
  (avl-tree-create #'dlenv-trie-node--ordering))

(defsubst dlenv-trie--get-leaf (node)
  "Returns the value of a Trie node. Unlike
`dlenv-trie-node--leaf', this function first tests if the NODE is
`nil'."
  (if (null node) nil (dlenv-trie-node--leaf node)))

(defsubst dlenv-trie--set-leaf (node leaf)
  "Set the value of a Trie node. Returns the (possibly `nil')
NODE. Unlike using `setf' to set the node value, this function
creates new NODE if the given NODE is `nil'."
  (if (null node)
      (if (null leaf) nil (make-dlenv-trie-node- :leaf leaf))
    (setf (dlenv-trie-node--leaf node) leaf)
    (if (dlenv-trie--null node) nil node)))

(defsubst dlenv-trie--get-branches (node)
  "Get the branches (an avl-tree) of a Trie node, might return
`nil'. The difference between this and
`dlenv-trie-node--branches' is that it tests if the given NODE is
`nil'."
  (if (null node) nil (dlenv-trie-node--branches node)))

(defsubst dlenv-trie--set-branches (node branches)
  "Set the BRANCHES value of a Trie NODE, replacing the previous
BRANCHES. Returns the NODE."
  (when (and (not (null branches)) (avl-tree-empty branches))
    (setq branches nil))
  (if (null node)
      (if (null branches) nil
        (make-dlenv-trie-node- :branches branches))
    (setf (dlenv-trie-node--branches node) branches)
    node))


(defun dlenv-trie--new1 (leaf alist)
  "Create a new Trie with a 1-level deep subtrie. Initialize it
with a list of cons cells, where each cons cell associates a
string to a value. Returns `nil' if the given ALIST argument is
`nil'."
  (let ((branches (dlenv-trie--new-branches)))
    (dolist (assoc alist)
      (avl-tree-enter
       branches
       (make-dlenv-trie-node-
        :segment (car assoc)
        :leaf (cdr assoc))))
    (make-dlenv-trie-node-
     :leaf leaf
     :branches branches)))

;; -------------------------------------------------------------------------------------------------
;; Using functions to perform in-place updates to `dlenv-trie-node-' elements.

(cl-defstruct
    (dlenv-trie-update
     (:type vector))
"This data structure is used by functions which can update
portions of a Trie in place. They are returned by lambda
functions that are passed as arguments to functions like
`dlenv-trie--with-leaf' and `dlenv-trie--with-branches'. It is
constructed with two fields:

1. `update' is the updated element which is used to replace the
   `leaf', the `branches', or the `node' in the structure
   iteself.

2. `return' is an arbitrary return value, typically a leaf value
   or an integer computed by counting elements in the Trie."
  (update nil)
  (return nil))


(defun dlenv-trie--lookup-branch1 (node key k)
  "Lookup a sub-Trie only 1 level deep within a Trie node. Return
a new empty node if the given NODE is `nil'."
  (when node
    (let ((branches (dlenv-trie--get-branches node)))
      (if (null branches) nil
        (avl-tree-member
         branches
         (make-dlenv-trie-node-
          :segment (elt key k)))))))


(defun dlenv-trie--delete-branch1 (node key k subnode)
  "Delete the given SUBNODE from the `:branches' of the given
NODE. If SUBNODE is `nil' this function does nothing. The SUBNODE
is deleted regardless of whether the SUBNODE is empty, so it
would be a good idea to call `dlenv-trie--null' on SUBNODE before
calling this function. NODE is returned unless it is null
according to `dlenv-trie--null', in which case `nil' is
returned. The SUBNODE is checked with
`dlenv-trie-node--assert-segment', the values KEY and K are only
used for error reporting."
  (when (and node subnode)
    (let ((branches (dlenv-trie-node--branches node)))
      (when branches
        (dlenv-trie-node--assert-segment subnode key k)
        (avl-tree-delete branches subnode)
        (dlenv-trie--set-branches node branches)
        (if (dlenv-trie--null node) nil node)))))


(defun dlenv-trie--insert-branch1 (node key k subnode)
  "Insert a SUBNODE element directly into the BRANCHES of the
given NODE, creating a NODE if it is `nil', and overwriting any
previous nodes with the same `:segment' as the given SUBNODE if
NODE is not `nil'. If SUBNODE is `nil' this function behaves as
`dlenv-trie--delete-branch1'. The SUBNODE is checked with
`dlenv-trie-node--assert-segment', the values KEY and K are only
used for error reporting."
  (if (dlenv-trie--null subnode)
      (dlenv-trie--delete-branch1 node key k subnode)
    (dlenv-trie-node--assert-segment subnode key k)
    (let ((branches (dlenv-trie--get-branches node)))
      (unless branches
        (setq branches (dlenv-trie--new-branches)))
      (avl-tree-enter branches subnode)
      (dlenv-trie--set-branches node branches))))


(defun dlenv-trie--insert (node key k leaf &optional update-val)
  "Using a KEY and starting from index K in the key, insert a
chain of Trie nodes each with an element from KEY (after index K)
as the node identifier. If UPDATE-VAL is supplied, it is called
with two arguments: first the previous value associated with the
given key (possibly `nil'), and second, the given LEAF argument
before storing it into the Trie at the given key. The UPDATE-VAL
function need only return a new LEAF, it need *not* construct a
`dlenv-trie-update' structure."
  (cond
   ((eq k (length key))
    (unless (null update-val)
      (setq leaf (funcall update-val (dlenv-trie--get-leaf node) leaf)))
    (dlenv-trie--set-leaf node leaf))
   ((and (< k (length key)) (>= k 0))
    (let ((subnode (dlenv-trie--lookup-branch1 node key k)))
      (setq subnode (dlenv-trie--insert subnode key (1+ k) leaf update-val))
      (if (dlenv-trie--null subnode)
          (dlenv-trie--delete-branch1 node key k subnode)
        (setf (dlenv-trie-node--segment subnode) (elt key k))
        (dlenv-trie--insert-branch1 node key k subnode))))
   (t
    (error (format "key element index %i out of bounds for key %S" k key)))))


(defun dlenv-trie--new (root-val alist &optional update-val)
  "Create a new Trie with a list of key-value pairs. Each
key-value pair should have a vector of strings as the key, the
value may be anything at all. The `dlenv-trie--insert' function will
be called repeatedly with each key to insert each value. The
UPDATE-VAL argument is a function that can be used to unify
elements with identical keys, see the `dlenv-trie--insert'
documentation for details about how this function is called."
  (let ((trie (make-dlenv-trie-node- :leaf root-val)))
    (dolist (assoc alist)
      (dlenv-trie--insert trie (car assoc) 0 (cdr assoc) update-val))))


(defun dlenv-trie--lookup-nearest1 (node key k)
  "This function traverses the given Trie NODE with a KEY path
starting from path segment number K. The traversal proceeds as
far as it can, and simply returns a cons cell containing in `car'
the non-`nil' value found, and in `cdr' an integer value
indicating the maximum key depth to which the traversal could
reach to find a non-`nil' subnode within NODE. The maximum depth
is returned which is greater than or equal to K except when no
branches are found at all, in which case K-1 is returned. It is
usually easier to use `subtrie--lookup-nearest' rather than this
function."
  (let ((len (length key))
        (leaf (dlenv-trie--get-leaf node)))
    (cond
     ((null node) (cons nil (1- k)))
     ((eq k len)
      (if (null leaf) (cons nil (1- k)) (cons node k)))
     ((and (>= k 0) (< k len))
      (let ((result
             (dlenv-trie--lookup-nearest1
              (dlenv-trie--lookup-branch1 node key k)
              key
              (1+ k))))
        (if (null (car result))
            (if (null leaf) (cons nil (1- k)) (cons node k))
          result)))
     (t
      (error (format "key element index %i out of bounds for key %S" k key))))))

;; -------------------------------------------------------------------------------------------------
;; High-level C.R.U.D. functions for working with Tries

(defun dlenv-trie--lookup-nearest (node key k &optional default-val)
  "Lookup the nearest element to the given KEY array starting
from index K in the array. The \"nearest element\" means when
walking along the branches of the tree with the list of KEY
elements, always keep the most recent value found along the path,
but if at a later point in the walk another value is found, that
value becomes the new \"nearest element.\" A vector of 3 elements
are always returned, the 0th element being the lookued-up value
or DEFAULT-VAL if nothing was found. The next two KEY sequences
returned are the list of elements of the KEY leading up to the
match, and the elements of the KEY that did not match. If no
elements are found the DEFAULT-VAL is retuend with an empty
vector as the list of key elements that matched and the original
KEY as the list of elements did not match."
  (let*((result (dlenv-trie--lookup-nearest1 node key k))
        (found-node (car result)))
    (if (or (null found-node) (< (cdr result) k))
        (make-dlenv-registered-
         :node-env nil
         :proj-dir (seq-take key k)
         :file-path (seq-drop key k))
      (make-dlenv-registered-
       :node-env (dlenv-trie--get-leaf found-node)
       :proj-dir (dlenv-path--proj-dir key (cdr result))
       :file-path (dlenv-path--file-path key (cdr result))))))


(defun dlenv-trie--update-nearest (node key k update-val)
  "Lookup the \"nearest element\" that exists from element K of
the the given KEY array, similar to how
`dlenv-trie--lookup-nearest' works. If a value exists anywhere
along the path specified by the KEY from element K then evaluate
UPDATE-VAL with two arguments:

1. the `dlenv-registered--node-env' value

2. the depth KD within the KEY path at which the update will
   occur, where KD is always less than or equal to K. You can use
   this depth value to split the KEY using `dlenv-key--proj-dir'
   and `dlenv-key--file-path' on KEY 

The result of UPDATE-VAL is then stored back into into the
tree. If no elements exist along the KEY path, do not evaluate
UPDATE-VAL at all, and return nil. Otherwise return the result of
UPDATE-VAL. This function is simpler than calling
`dlenv-trie--lookup-nearest' and updating the leaf of the
`dlenv-registered-' structure returned."
  (let*((result (dlenv-trie--lookup-nearest1 node key k))
        (found-node (car result)))
    (if (or (null found-node) (< (cdr result) k)) nil
      (let ((ret (funcall update-val (dlenv-trie--get-leaf found-node) (cdr result))))
        (dlenv-trie--set-leaf found-node ret)
        ret))))


(defun dlenv-trie--delete (node key k)
  "Delete the value at KEY in NODE. This function necessarily
changes the state of NODE without adding anything to it, so NODE
must be non-`nil' or else it does nothing at all. If the value
deleted was the last element on that branch of the Trie, the
branch is also deleted. Returns the value deleted."
  (cond
   ((or (null node) (> k (length key)) (< k 0)) nil)
   ((eq k (length key))
    (let ((ret (dlenv-trie--get-leaf node)))
      (dlenv-trie--set-leaf node nil)
      ret))
   ((let ((subnode (dlenv-trie--lookup-branch1 node key k)))
      (if (null subnode) nil
        (let ((ret (dlenv-trie--delete subnode key (1+ k))))
          (when (dlenv-trie--null subnode)
            (dlenv-trie--delete-branch1 node key k subnode))
          ret))))))

;; -------------------------------------------------------------------------------------------------
;; Global state

(unintern 'dir-local-env-all-configs)

(defvar dir-local-env-all-configs (make-dlenv-trie-node-)
  "Any directory which has environment properties set for it are
cached in this global variable. It is similar to the
`dir-local-directory-cache' but is queried by functions which
care about the directory-specific environment such as
`make-process' and `start-process', so it serves the environment
on demand. There is no reason to propagate these environment
vairables to each buffer's buffer-local variables where they will
be persisted until the buffer is deleted.")

;; -------------------------------------------------------------------------------------------------
;; Parsing trie keys from directory path strings.

(defsubst dlenv--key-to-path (path)
  "Inverse of `dlenv--path-to-key'."
  (string-join path "/"))


(define-error 'dir-local-env-path-error
  "Path to directory for declaring a dir-local-env"
  'file-error)


(defun dlenv--path-to-key (&optional path)
  "Parse from a file PATH argument of a string type (defaults to
`default-directory') a trie key that can be used to lookup a
directory environment from the `dir-local-env-all-configs'
trie. This also involves testing whether the path is a file or
directory, it must exist in the current filesystem or else an
error is returned. If the given PATH argument is of a vector
type, assume it is a list of strings that was produced by passing
a string path to this function and return it unchanged."
  (setq path (expand-file-name (or path default-directory)))
  (let*((attrs (file-attributes path))
        (make-key
         (lambda (path)
           (let ((segments (f-split path)))
             (when (equal "/" (car segments))
               (setq segments (cons "" (cdr segments))))
             (vconcat segments)))))
    (cond
     ((null attrs)
      (signal 'dir-local-env-path-error
       (list "does not exist" :path path)))
     ((car attrs) ; car of this list should be `t' if it is a directory
      (funcall make-key path))
     ((or (stringp (car attrs)) ; if car is a string, it is a symlink
          (null (car attrs))) ; if car is nil, it is a regular file
      (funcall make-key (file-name-directory path)))
     (t
      (signal
       'dir-local-env-path-error
       (list
        "`file-attributes' function returned unexpected ATTRIBUTES data for file path"
        :path path
        :attributes attrs))))))


(defsubst dlenv-path--proj-dir (key k)
  "Given a KEY constructed by `dlenv--path-to-key' and an integer
K indicating the depth of some element along the path KEY, return
the portion of KEY that represents the project directory."
  (seq-take key k))


(defsubst dlenv-path--file-path (key k)
  "Given a KEY constructed by `dlenv--path-to-key' and an integer
K indicating the depth of some element along the path KEY, return
the portion of KEY that represents the file path relative to the
projcet directory."
  (seq-drop key k))

;; -------------------------------------------------------------------------------------------------
;; Functions for inspecting directory local environment declarations, whether they be ALISTs or
;; macro expressions.

(define-error 'dir-local-env-error
  "Variable declaration for dir-local-env"
  'wrong-type-argument)


(defun dlenv--check-varlist-syntax (do-eval varlist)
  "Check the syntax of a VARLIST. If DO-EVAL is non-`nil' it must
have the same syntax as the `let*' macro and may contain `:alist'
keywords. If DO-EVAL is `nil' then the only check performed is
that the `car' of each VARLIST element must satisfy the `symbolp'
predicate (thus the VARLIST must *not* contain `:alist'
keywords). Any syntax errors found will result in a `throw' with
information about where the error occurred."
  (unless (or (consp varlist) (null varlist))
    (signal
     'dir-local-env-error
     (list
      "expected varlist"
      (list :is varlist))))
  (let ((assoc-count 0))
    (if do-eval
        (dolist (assoc varlist)
          (let ((sym (car assoc)))
            (cond
             ((and (keywordp sym) (not (eq :alist sym)))
              (signal
               'dir-local-env-error
               (list
                "unknown keyword"
                :nth assoc-count
                :key sym)))
             ((not (symbolp sym))
              (signal
               'dir-local-env-error
               (list
                "first element of variable delclaration form is not a symbol"
                :nth assoc-count
                :type (type-of sym)
                :is sym)))
             ((and (not (null (cdr assoc)))
                   (not (null (cadr assoc)))
                   (not (null (cddr assoc))))
              (signal
               'dir-local-env-error
               (list
                "extraneous elements in variable declaration form"
                :nth assoc-count
                :extra (cddr assoc))))
             (t (setq assoc-count (1+ assoc-count))))))
      (dolist (assoc varlist)
        (let ((sym (car assoc)))
          (when (or (keywordp sym) (not (symbolp sym)))
            (signal
             'dir-local-env-error
             (list
              "first element of variable declaration form is not a symbol"
              :nth assoc-count
              :type (type-of sym)
              :is sym))))))))


(defun dlenv--new-env-from-alist (do-eval varlist &optional env)
  "Assign values to symbols in the given ENV from an ALIST. ENV
must be an obarray or nil, in which case a new obarray is
constructed. If DO-EVAL is non-`nil' then the semantics of
VARLIST is the same as the VARLIST in the `let*' macro, i.e. the
`cadr' of each VARLIST element is evaluated with `eval', and each
element of VARLIST must contain no more than 2 elements, as in
the following syntax:

    ((SYMBOL FORM)
     (SYMBOL FORM)
     ...)

or of the form:

    ((:alist FORM)
     (:alist FORM)
     ...)

and you may mix ordinary symbol forms and `:alist' forms:

    ((SYMBOL FORM)
     (:alist FORM)
     (SYMBOL FORM)
     (:alist FORM)
     ...)

in which case, the keyword `:alist' indicates that FORM must be
evaluated with `eval' and the result must be an alist which is
then added to the environment being constructed. This is a good
way to inherit environment variables from other places.

If DO-EVAL is `nil' then it is assumed that the VARLIST is
actually an ordinary ALIST, `:alist' keywords are *not* allowed,
as in the following syntax:

    ((cons 'SYMBOL VALUE)
     (cons 'SYMBOL VALUE)
     ...)

or

    '((SYMBOL . VALUE)
      (SYMBOL . VALUE)
      ...)

or perhaps

    `((SYMBOL . ,FORM)
      (SYMBOL . ,FORM)
      ...)

If evaluation completes successfully, an obarray is returned with
all symbols set to their associated (possibly evaluated) values."
  ;; Make sure ENV is an obarray
  (cond
   ((null env)
    (setq env (obarray-make)))
   ((not (obarrayp env))
    (signal
     'dir-local-env-error
     (list
      "`dlenv--new-env-from-alist' expected obarray as third argument"
      :type (type-of env)
      :is env))))
  ;; Check syntax, throw a signal if syntax is not OK.
  (dlenv--check-varlist-syntax do-eval varlist)
  ;; Now contruct the environment.
  (if (null do-eval)
      (dolist (assoc varlist)
        ;; This loop treats the VARLIST as an ordinary ALIST
        (let ((var (car assoc))
              (val (cdr assoc)))
          (put (intern (symbol-name var) env) 'value val)))
    ;; ...else we evaluate VARLIST with the same semantics as `let*'
    (let ((assoc-count 0)
          (env-alist nil))
      (dolist (assoc varlist)
        (let*((define
                (lambda (var val)
                  (put (intern (symbol-name var) env) 'value val)
                  (setq env-alist (cons (cons var val) env-alist))))
              (var (car assoc))
              (form (cadr assoc))
              (val nil))
          (fset 'define define)
          (condition-case err
              (setq val (eval form env-alist))
            ((debug error)
             (signal
              'dir-local-env-error
              (list
               "form evaluation failed"
               :nth assoc-count
               :form form
               :error err))))
          (if (eq :alist var)
              (progn
                (condition-case err
                    (dlenv--check-varlist-syntax nil val)
                  (dir-local-env-error
                   (signal
                    'dir-local-env-error
                    (list
                     ":alist form evaluated to invalid alist value"
                     :nth assoc-count
                     :form form
                     :error err))))
                (dolist (assoc2 val)
                  (let ((var2 (car assoc2))
                        (val2 (cdr assoc2)))
                    (define var2 val2))))
            (define var val)
            (setq assoc-count (1+ assoc-count)))))))
  env)


(defun dlenv--register (path do-eval &optional alist)
  "Check that PATH is valid with `dlenv--path-to-key', construct
a new environment with `dlenv--new-env-from-alist' passing
DO-EVAL and ALIST as arguments, then assign the newly constructed
environment to the `dir-local-env-all-configs' global variable
using the `dlenv-trie--insert' function.'"
  (setq path (dlenv--path-to-key path))
  (let ((env-node (dlenv-trie--lookup-nearest dir-local-env-all-configs path 0))
        (env nil)
        (result nil))
    (if (or (null env-node) (not (null (dlenv-registered--node-env env-node))))
        (message
         (format
          "ignored directory %S, already registered"
          (dlenv--key-to-path path)))
      (condition-case err
          (setq env (dlenv--new-env-from-alist do-eval alist))
        (dir-local-env-error
         (signal
          'dir-local-env-error
          (list
           "bad dir-local-env declaration for"
           :directory (dlenv--key-to-path path)
           :error err))))
      (if (dlenv-trie--insert dir-local-env-all-configs path 0 nil (lambda (_ _) env))
          (message (format "Registered dir-local-env: %S" (dlenv--key-to-path path)))
        (error "`dlenv-trie--insert' evaluated to nil")))))


(defsubst dir-local-env-register (&optional path &rest alist)
  "Register the current `default-directory' into the
`dir-local-env-all-configs' registry, an in-memory database
containing directory local configuration variables. Once
registered, you may set directory local variables using
`dir-local-env--change-config'. Directory local variables are not
applied directly, but may be used by hook functions using
`dir-local-env--lookup'. This function will create a new empty
`avl-tree' which associates keys of type `symbolp' with arbitrary
values. If the give PATH is already registered, no change is
made and this function is a no-op."
  (interactive "D")
  (dlenv--register path nil alist))


(defun dir-local-env-unregister (&optional path)
  "Unregister the current `default-directory' (or PATH if given)
from the `dir-local-env-all-configs' registry. If the
`default-directory' or PATH have not been registered with
`dir-local-env-register', this function does nothing."
  (interactive "D")
  (setq path (dlenv--path-to-key path))
  (let ((result (dlenv-trie--delete dir-local-env-all-configs path 0)))
    (if (null result)
        (message (format "Not a registered dir-local-env: %S" (dlenv--key-to-path path)))
      (message (format "Successfully UN-registered dir-local-env: %S" (dlenv--key-to-path path))))))


(defsubst dlenv--project-dir-node (&optional path)
  "For the current `default-directory' (or PATH if given),
get the dlenv-trie node from the `dir-local-env-all-configs' tree
for the nearest parent directory (or for itself) that has been
registered by `dir-local-env-register'."
  (setq path (dlenv--path-to-key path))
  (dlenv-trie--lookup-nearest dir-local-env-all-configs path 0))


(defun dlenv--project-dir-path (&optional path)
  "For the current `default-directory' (or PATH if given),
get the file path of the nearest parent directory (or itself)
that has been registered by `dir-local-env-register'."
  (let ((env-node (dlenv--project-dir-node path)))
    (when env-node (dlenv--key-to-path (dlenv-registered--proj-dir env-node)))))


(defun dlenv--project-dir-env (&optional fail-unregistered path)
  "For the current `default-directory' (or PATH if given),
get the avl-tree of the nearest parent directory (or itself) that
has been registered by `dir-local-env-register'. Setting the
FAIL-UNREGISTERED argument to a non-`nil' function symbol will
cause this function to throw an error if the `default-directory'
or PATH is not registered with `dir-local-env-register', the
error message will report the symbol assigned to
`fail-unregistered'."
  (unless disable-dir-local-env
    (let ((env-node (dlenv--project-dir-node path)))
      (if (or (null env-node) (null (dlenv-registered--node-env env-node)))
          (unless (null fail-unregistered)
            (error (format "%S: called on unregistered path %S" fail-unregistered path)))
        (dlenv-registered--node-env env-node)))))


(defun dir-local-env-show-all (&optional path)
  "For the current `default-directory' (or PATH if given),
retrieve the dir-local environment defined for it. This will
create a buffer \"*dir-local-env*\" which displays the list of
all variables set by `dir-local-env-set-env'."
  (interactive "D")
  (let ((env-node (dlenv--project-dir-node path))
        (file (or (buffer-file-name) default-directory)))
    (if (or (null env-node) (null (dlenv-registered--node-env env-node)))
        (error
         (format
          "Current buffer not a member of any directory registered by `dir-local-env-register': %S"
          file))
      (let*((env (dlenv-registered--node-env env-node))
            (project-path (dlenv--key-to-path (dlenv-registered--proj-dir env-node)))
            (bufname (buffer-name))
            (dispbuf (get-buffer-create "*dir-local-env*"))
            (disable-sym
             (or (intern-soft "disable-dir-local-env" env)
                 (intern-soft "disable-dir-local-env")))
            (is-disabled (when disable-sym (not (null (get disable-sym 'value))))))
        (with-current-buffer dispbuf
          (read-only-mode 0)
          (erase-buffer)
          (insert (format "(buffer-name . %S)\n" bufname))
          (insert (format "(buffer-file-name . %S)\n" file))
          (insert (format "(dir-local-env . %S)\n" project-path))
          (insert (format "(disable-dir-local-env . %S)\n" is-disabled))
          (insert ";; ----------------------------------------------------------------------\n")
          (when is-disabled
            (insert ";; NOTE: all of the below variables are IGNORED because `disable-dir-local-env' is non-`nil'.\n"))
          (unless (null env)
            (mapatoms
             (lambda (sym) (insert (format "(%S . %S)\n" sym (get sym 'value))))
             env))
          (read-only-mode 1))
        (display-buffer dispbuf)))))


(defsubst dlenv--get-env (env var)
  "This function looks-up a variable VAR in an environment ENV,
as long as ENV has been returned by the
`dlenv--get-project-dir-env' function and is not `nil' (and this
does not check if ENV is `nil', and will throw an exception if it
is)."
  (let ((sym (intern-soft (symbol-name var) env)))
    (get sym 'value)))


(defun dir-local-env-get (var &optional path)
  "Get an environment variable VAR for the current
`default-directory' (or PATH if given), assuming the
`default-directory' or one of it's parent directories have been
registered with `dir-local-env-register'. This function fails
silently (returns `nil') if the `default-directory' or PATH is
not registered with `dir-local-env-register', or if the VAR is
undefined."
  (let ((env (dlenv--project-dir-env nil path)))
    (unless (null env) (dlenv--get-env env var))))


(defun dir-local-env-set (var value &optional path)
  "Set an environment variable VAR to VALUE for the current
`default-directory'' (or PATH if given), assuming the
`default-directory' or one of it's parent directories have been
registered with `dir-local-env-register' function. If
`default-directory' or PATH have not been registered with
`dir-local-env-register' an error condition is raised."
  (let ((env (dlenv--project-dir-env 'dir-local-env-set path)))
    (unless (null env)
      (let ((sym (intern (symbol-name var) env)))
        (put sym 'value value)))))


(defun dir-local-env-del (var &optional path)
  "Delete an environment variable VAR for the current
`default-directory' (or PATH if given) , assuming the
`default-directory' or one of it's parent directories have been
registered with `dir-local-env-register' function. If
`default-directory' or PATH have not been registered with
`dir-local-env-register' an error condition is raised."
  (let ((env (dlenv--project-dir-env 'dir-local-env-set path)))
    (unless (null env) (unintern (symbol-name var) env))))


(defun dir-local-env-modify-var (var update-fn &optional path)
  "If VAR has been set in the current `default-directory' (or
PATH if given), modify the value associated with that VAR using
the given UPDATE-FN, assuming the `default-directory' or one of
it's parent directories have been registered with
`dir-local-env-register' function. If `default-directory' or PATH
have not been registered with `dir-local-env-register' an error
condition is raised."
  (let*((env (dlenv--project-dir-env 'dir-local-env-set path)))
    (when env
      (let ((sym (intern-soft (symbol-name var) env))
            (new-val (when sym (funcall update-fn (get sym 'value)))))
        (when new-val (put sym 'value new-val))
        new-val))))

;; -------------------------------------------------------------------------------------------------
;; Functions for obtaining a new process environment

(defun dlenv--split-null-delimited-string (str)
  "The best way to get a new process environment is to run a
command such as `printenv -0` in a shell buffer. This function
can parse null-character (\"\0\") delimited strings into a
list-of-strings data structure that suitable for use as a
`process-environment'."
  (mapcar #'substring-no-properties (split-string str "\0" t)))


(defun dlenv--check-shell-env-data-struct (env)
  "Checks that the ENV is a sequence data structure, preferrably
a list, which contains only strings that match the regular
expression \"^[[:alnum:]_]+[=]\", in other words, a string that
properly sets a shell environment variable. If all elements of
the list are OK, this function returns t. If any element is
incorrect, an error is thrown."
  (let ((i 0))
    (dolist (var env)
      (if (posix-string-match "^[[:alnum:]_]+[=]" var)
          (setq i (1+ i))
        (error
         (format "Not a valid environment variable: (nth %i) == %s" i var))))
    t))


(defun dlenv--exec-get-env (varname)
  "If the current `dir-local-env' has the `process-environment'
variable set, lookup what we are calling an
\"exec-env-var\" (e.g. a shell environment variable used in a
Bash process) environment variable within the
`process-environment'. The VARNAME must be a string that is a
valid shell environment variable name."
  (setq varname (concat varname "="))
  (let ((execenv (dir-local-env-get 'process-environment)))
    (while
        (and
         (not (null execenv))
         (not (string-prefix-p varname (car execenv))))
      (setq execenv (cdr execenv)))
    (unless (null execenv)
      (substring (car execenv) (length varname)))))


(defsubst dlenv--exec-var-unset-p (value)
  "A predicate that evaluates to `t' when VAUE is either `nil' or
is the empty string \"\"."
  (or (null value) (string-empty-p value)))


(defun dlenv--exec-set-env (varname value)
  "If the current `dir-local-env' has the `process-environment'
variable set, lookup what we are calling an
\"exec-env-var\" (e.g. a shell environment variable used in a
Bash process) environment variable within the
`process-environment' and change the environment variable given
by VARNAME to VALUE. The VARNAME must be a string that is a valid
shell environment variable name. The VALUE must be either a
string, or it must be a function that takes a string and returns
a string."
  (setq varname (concat varname "="))
  (let*((execenv (dir-local-env-get 'process-environment))
        (orig-execenv execenv))
    (while
        (and
         (not (null execenv))
         (not (string-prefix-p varname (car execenv))))
      (setq execenv (cdr execenv)))
    (if (null execenv)
        (progn
          (when (functionp value)
            (setq value (funcall value "")))
          (unless (dlenv--exec-var-unset-p value)
            (dir-local-env-set
             'process-environment
             (cons (concat varname value) orig-execenv))))
      (when (functionp value)
        (setq value (funcall value (substring (car execenv) (length varname)))))
      (setcar execenv (concat varname value)))))


(defun dlenv--induce-exec-path ()
  "Set the `exec-path' for the `dir-local-env' using the \"PATH\"
environment variable defined in `process-environment'. This only
works if `process-environment' has been set by
`dir-local-env-set' function, otherwise this function does
nothing."
  (let ((new-exec-path (parse-colon-path (dlenv--exec-get-env "PATH"))))
    (unless (null new-exec-path)
      (dir-local-env-set 'exec-path new-exec-path))))


(defun dlenv--generate-random-delimiter (&optional entropy)
  "Generate a delimiter that can be used to uniquly identify some
section of text in a stream of line-delimited text -- this is
intended to be used for inserting markers into asynchrnous
process buffers. If you keep the random delimiter string
somewhere as a variable in your program, you can then search the
buffer for this string and be fairly certain that the string
found was indeed the very same string you inserted into the
stream to identify it. Takes an optional integer argument ENTROPY
which controls how many random bytes to generate.

- The ENTROPY argument is clamped to a value between 10 and 167,
  which guarantees a delimiter of at least 70 characters and at
  most 1022 characters.

- The `base64-encode-string' function is used to generate the
  string from a string of random bytes.

- The delimiter string itself is guaranteed to be visible to the
  human eye (it contains many dash (-) characters), and it is
  guaranteed to only contain characters that match the regexp
  \"[-/+[:alnum:]]+\".

- The delimiter never contains spaces or line breaking
  characters."
  (setq entropy (if entropy (min 167 (max 4 entropy)) 10))
  (with-temp-buffer
   (insert-char ?- 10)
   (insert
    (with-temp-buffer
      (dotimes (_ (* 3 entropy)) (insert (random 256)))
      (base64-encode-string (buffer-string))))
   (goto-char 11)
   (dotimes (_ entropy)
     (insert ?-)
     (forward-char 4)
     (insert ?-))
   (insert-char ?- 10)
   (buffer-string)))

;; -------------------------------------------------------------------------------------------------
;; Functions interfacing to project.el

(defun dlenv--project-try (path)
  "This function is to be installed into the
`project-find-functions' list of hooks for finding project
directories. If a subpath of PATH is has been registered with
`dir-local-env-register', and the `project-dir-disabled' variable
is unset or `nil', then this function returns a path that can be
used with the various CL-generic functions defined in the
project.el package."
  (let*((env-node (dlenv--project-dir-node path))
        (env (dlenv-registered--node-env env-node))
        (disabled
         (or (null env)
             (dlenv--get-env env 'project-dir-disabled)
             (dlenv--get-env env 'disable-dir-local-env))))
    (when (null disabled)
      (cons 'dir-local-env (dlenv--key-to-path (dlenv-registered--proj-dir env-node))))))


(defun dlenv--get-env-list-or-func (sym &optional path)
  "This method is used to look up certain variables in the
dir-local-env using `dlenv--get-env', and check that the value is
`nil', a `listp', or a `function' type. If it is a function, it
evaluates the function. Otherwise an error message is reported."
  (let*((env (dlenv--project-dir-env path))
        (val (when env (dlenv--get-env env sym))))
    (cond
     ((null val) nil)
     ((consp val) val)
     ((vectorp val) val)
     ((functionp val) (funcall val path))
     (t (error
         (concat
          "dir-local-env: the symbol '" (symbol-name sym)
          " is set to an non-list or non-function value, use"
          " (dir-local-env-set 'project-external-roots ...) to correct this."))))))

(when (require 'project nil t)

  (setq project-find-functions
        (cons #'dlenv--project-try
              (delq #'dlenv--project-try project-find-functions)))

  (cl-defmethod project-root ((project (head dir-local-env)))
    "The PROJECT will have been constructed by
`dlenv--project-try', simply extract the root directory element
from this object."
    (cdr project))

  (cl-defmethod project-external-roots ((project (head dir-local-env)))
    "This method is used by project.el to find external
libraries (e.g. package dependencies, documentation) related to
the project. To set external roots for a project, use
`dir-local-env-set' and set the `project-external-roots' symbol
to a list of absolute paths to external root directories."
    (dlenv--get-env-list-or-func 'project-external-roots (cdr project)))

  (cl-defmethod project-ignores ((project (head dir-local-env)) dir)
    "This function should return a list of glob patterns of
files to ignore. The DIR given may be a `project-external-root'."
    (dlenv--get-env-list-or-func 'project-ignores (cdr project)))

  ;; TODO: `project-files' and `project-buffers' are not overloaded
  ;; because the default implementation should be triggered. I would
  ;; like to trigger the default implementation if the dir-local-env
  ;; does not specify a `project-files' or `project-buffers' function,
  ;; but I don't know how to do this yet.

  (message "dir-local-env: set hooks for \"project\" functionality."))


(when (require 'eglot nil t)

  (defun dlenv--eglot-server-programs (fun &rest args)
    "This is an advice function set for `eglot--guess-contact',
which sets the `eglot-server-programs' variable using
`dir-local-env-get'."
    (let ((programs (dir-local-env-get 'eglot-server-programs)))
      (if (null programs)
          (funcall fun args)
        (let ((eglot-server-programs programs))
          (message (format "dir-local-env set eglot-server-programs to %S" eglot-server-programs))
          (funcall fun args)))))

  (defun dlenv--enable-eglot-mode (enable)
    "If the ENABLE argument is non-`nil', add advice to the
`eglot--guess-contact' function such that the
`eglot-server-programs' variable is set from the dir-local-env
variable of the same name if it is defined and can be retrieved
by `dir-local-env-get'. With this mode enabled, you can declare
an alist of exactly which language server protocol server
executables you would like to use for each language mode by
setting the `eglot-server-programs' variable with
`dir-local-env-set'. The format of this variable should be
identical to that of `eglot-server-programs'."
    (if (and enable (or (symbolp enable) (> enable 0)))
        (progn
          (add-function
           :around (symbol-function 'eglot--guess-contact) #'dlenv--eglot-server-programs)
          (message "Enabled dir-local-env hook on function `eglot--guess-contact'"))
      (remove-function
       (symbol-function 'executable-find) #'dlenv--eglot-server-program)
      (message "Disabled dir-local-env hook on function `eglot--guess-contact'")))  
  
  (dlenv--enable-eglot-mode t))

;; -------------------------------------------------------------------------------------------------
;; Functions for enabling or disabling the dir-local-env global minor mode.

(defun dlenv--dispatch-make-process (fun &rest args)
  "Advice function used to alter the behavior of `make-process'
so that it uses a different `process-environment' retrieved by
`dir-local-env-get' when spawning the child process."
  (let ((new-process-environment (dir-local-env-get 'process-environment)))
    (if (and new-process-environment (consp new-process-environment))
        (let ((dlenv--project-dir-path (dlenv--project-dir-path))
              (process-environment new-process-environment))
          (message
           (format
            "`process-environment' set to dir-local-env for %S"
            dlenv--project-dir-path))
          (apply fun args))
      (apply fun args))))


(defun dlenv--dispatch-executable-find (fun &rest args)
  "Advice function used to alter the behavior of
`executable-find' so that it uses a different `exec-path'
retrieved by `dir-local-env-get'."
  (let ((new-exec-path (dir-local-env-get 'exec-path)))
    (if (and new-exec-path (consp new-exec-path))
        (let ((dlenv--project-dir-path (dlenv--project-dir-path))
              (exec-path new-exec-path))
          (message
           (format
            "`exec-path' set to dir-local-env for %S"
            dlenv--project-dir-path))
          (apply fun args))
      (apply fun args))))


(defun dlenv--dispatch-hack-dir-local-variables (fun &rest args)
  "Advice function used to alter the behavior of
`hack-dir-local-variables' so that it populates the
`dir-local-variables-alist' before it gets populated by the
`.dir-locals.el' file. The variable values in the
`.dir-locals.el' file will take precedence over the
`dir-local-env' definitions. *Note* that
`enable-dir-local-variables' and `enable-local-variables' must
both be non-nil for this function to do anything at all."
  (if (and enable-local-variables enable-dir-local-variables)
      (let ((env-node (dlenv--project-dir-node)))
        (unless (or (null env-node) (null (dlenv-registered--node-env env-node)))
          (mapatoms
           (lambda (sym) (push (cons sym (get sym 'value)) dir-local-variables-alist))
           (dlenv-registered--node-env env-node))
          (message
           (format
            "dir-local vairables applied from dir-local-env for %S"
            (dlenv--key-to-path (dlenv-registered--proj-dir env-node))))
          (apply fun args)))
    (apply fun args)))


(defun dir-local-env-global-minor-mode (enable)
  "If the ENABLE argument is non-`nil', add advice to the
`make-process' function such that any time an external process is
executed, the `process-environment' variable is set from the
dir-local-env variable of the same name if it is defined and can
be retrieved by `dir-local-env-get'."
  (if (and enable (or (symbolp enable) (> enable 0)))
      (progn
        (add-function
         :around (symbol-function 'hack-dir-local-variables) #'dlenv--dispatch-hack-dir-local-variables)
        (add-function
         :around (symbol-function 'make-process) #'dlenv--dispatch-make-process)
        (add-function
         :around (symbol-function 'call-process) #'dlenv--dispatch-make-process)
        (add-function
         :around (symbol-function 'call-process-region) #'dlenv--dispatch-make-process)
        (add-function
         :around (symbol-function 'executable-find) #'dlenv--dispatch-executable-find)
        (when (intern-soft "dlenv--enable-eglot-mode")
          (dlenv--enable-eglot-mode t))
        (message "Enabled dir-local-env hook on function `make-process', `call-process', `call-process-region'"))
    (remove-function
     (symbol-function 'hack-dir-local-variables) #'dlenv--dispatch-hack-dir-local-variables)
    (remove-function
     (symbol-function 'make-process) #'dlenv--dispatch-make-process)
    (remove-function
     (symbol-function 'call-process) #'dlenv--dispatch-make-process)
    (remove-function
     (symbol-function 'call-process-region) #'dlenv--dispatch-make-process)
    (remove-function
     (symbol-function 'executable-find) #'dlenv--dispatch-executable-find)
    (when (intern-soft "dlenv--enable-eglot-mode")
      (dlenv--enable-eglot-mode nil))
    (message "Disabled dir-local-env hook on function `make-process', `call-process', `call-process-region'")))

;; -------------------------------------------------------------------------------------------------

(defmacro defdir-local-env (&rest syms)
  "This macro allows you to declare a `dir-local-env' for various
directories. The arguments to this macro are sequence of
directory/environment pairs (alternating between a directory and
an environment), where the directory is a string to the directory
path, and the environment is a VARLIST with the same syntax and
semantics of the `let*' macro.

When this macro is evaluated, the function
`dir-local-env-register' is called, and then each `cdr' in the
environment alist is evaluated, with the result being assigned to
the variable in the `car'.

The directory must satisfy 2 properties in order to be registerd
by this macro:

  1. It must exist, and be a directory and not a file

  2. It must not already be registered by
     `dir-local-env-register' or a prior evaluation of the
     `defdir-local-env'.

As a result of the above 2 properties, this macro is
*idempotent*, meaning it is safe to evaluate a call to this macro
as many times as you want without causing unwanted cumulative
updates. It is expected you might declare directory-local
environments using calls to the `defdir-local-env' macro written
into a file such as \"dir-local-env.el\" that is `load'-ed from
within \"init.el\". You should be able to use the same
\"dir-local-env.el\" file at multiple sites without errors
occuring, and you should be able to create a directory and
re-`load' the \"dir-local-env.el\" file to register that
directory without causing a change to the environment of any
other registered directory.

The syntax of arguments takes a directory followed by a VARLIST
with the same syntax and semantics of the `let*' macro. For
example:
(defdir-local-env
  \"/path/to/first/dir\"  ((var-1A form-1A)
                           (var-1B form-1B)
                           ...
                           (var-1Z form-1Z))
  \"/path/to/second/dir\" ((var-2A form-2A)
                           (var-2B form-2B)
                           ...
                           (var-2Z form-2Z))
  ....
  \"/path/to/final/dir\"  ((var-ZA form-ZA)
                           (var-ZB form-ZB)
                           ...
                           (var-ZZ form-ZZ)))

Each FORM in the above example is evaluated, and the result of
evaluation is assigned to it's respective VAR. The VARLIST of
`defdir-local-env' has one difference from `let*' in that a
VARLIST element may also be of the form (:alist ALIST-FORM),
which evaluates ALIST-FORM, and the result value (which must be
an ALIST or else a error is signaled) is used to declare
variables for the directory local environment. This is a good way
to inherit ALISTs from other places into the directory local
environment. It is also possible to intermingle `:alist' forms
with ordinary variable declarations, for example:

(defdir-local-env
  \"/path/to/some/directory\" ((var-1A form-1A)
                               (:alist form-inheriting-1B)
                                ...))

This macro returns the number of directory local environments
that were configured. If it returns 0, it means all directory
paths specified in the form had already been registered. If it
returns greater than 0, it indicates that at least 1 directory
local environment that had not yet been registered is now
registered. Inspect the content of the *Messages* buffer to see
which directories were registered.

See also `dir-local-env-register' and `dir-local-env-unregister'."
  (let*((sym-count 0)
        (get-next
         (lambda ()
           (let ((result (car syms)))
             (setq sym-count (1+ sym-count))
             (setq syms (cdr syms))
             result)))
        (path nil)
        (alist nil))
    (fset 'get-next get-next)
    (while syms
      (setq path (get-next))
      (unless (stringp path)
        (signal
         'dir-local-env-error
         (list
          "expected string, path to directory"
          :nth sym-count
          :type (type-of path)
          :is path)))
      (setq alist (get-next))
      (unless (consp alist)
        (signal
         'dir-local-env-error
         (list
          "expected VARLIST (same syntax as `let*')"
          :nth sym-count
          :type (type-of alist)
          :is alist)))
      (condition-case err
          (dlenv--register path t alist)
        (dir-local-env-path-error
         (message (format "defdir-local-env: ignored nonexistent directory %S" path)))))))

;; -------------------------------------------------------------------------------------------------

(when nil
  ;; Tests.
  ;; Set the above (when nil ...) to (when t ...) to enable these tests.
  (save-excursion
    (switch-to-buffer-other-window "*test-output*<dir-local-env>")
    (erase-buffer) ;; This is a dangerous function, use it with care.
    (let ((trie)
          (show (lambda (trie) (insert (format "%S\n" trie)))))
      (fset 'show show)
      (setq trie (make-dlenv-trie-node-))
      (goto-char (point-max))
      ;;(dlenv-trie--insert trie [] 0 "root-node")
      ;;(show trie)
      ;;(show (dlenv-trie--lookup-nearest trie [] 0))
      (dlenv-trie--insert trie ["first"] 0 "1-level-down")
      ;;(show trie)
      (dlenv-trie--insert trie ["one" "A" "you"] 0 "one-A-you")
      ;;(show trie)
      (dlenv-trie--insert trie ["one" "A" "me"] 0 "one-A-me")
      ;;(show trie)
      (dlenv-trie--insert trie ["one" "B" "you"] 0 "one-B-you")
      ;;(show trie)
      (dlenv-trie--insert trie ["one" "B" "me"] 0 "one-B-me")
      ;;(show trie)
      (dlenv-trie--insert trie ["two" "A" "you"] 0 "two-A-you")
      ;;(show trie)
      (dlenv-trie--insert trie ["two" "A" "me"] 0 "two-A-me")
      ;;(show trie)
      (dlenv-trie--insert trie ["two" "B" "you"] 0 "two-B-you")
      ;;(show trie)
      (dlenv-trie--insert trie ["two" "B" "me"] 0 "two-B-me")
      ;;(show trie)
      (dlenv-trie--insert trie ["one" "A"] 0 "one-A")
      ;;(show trie)
      (dlenv-trie--insert trie ["one" "B"] 0 "one-B")
      ;;(show trie)
      (dlenv-trie--insert trie ["two" "A"] 0 "two-A")
      ;;(show trie)
      (dlenv-trie--insert trie ["two" "B"] 0 "two-B")
      ;;(show trie)
      (dlenv-trie--update-nearest trie ["one" "B" "this" "that"] 0 (lambda (str _) (s-upcase str)))
      ;;(show trie)
      (insert "-------------------\n")
      (show (dlenv-trie--lookup-nearest trie ["first"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "A" "you"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "A"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "B"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "B" "this" "that"] 0))
      (show (dlenv-trie--lookup-nearest trie ["two" "A" "you" "me"] 0))
      (show (dlenv-trie--lookup-nearest trie ["two" "A" "me" "them"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "A" "me" "us"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "A" "us" "them"] 0))
      (insert "-------------------\n")
      (dlenv-trie--delete trie ["one" "A"] 0)
      (dlenv-trie--delete trie ["two" "A" "you"] 0)
      (dlenv-trie--delete trie ["two" "A" "me"] 0)
      (show (dlenv-trie--lookup-nearest trie ["one" "A"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "A" "me" "us"] 0))
      (show (dlenv-trie--lookup-nearest trie ["one" "A" "us" "them"] 0))
      (show (dlenv-trie--lookup-nearest trie ["two" "A" "you" "me"] 0))
      (show (dlenv-trie--lookup-nearest trie ["two" "A" "me" "them"] 0))
      )))
