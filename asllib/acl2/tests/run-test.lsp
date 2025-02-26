

;; (assign :fname "ilog2-ast.lsp")

(in-package "ASL")

(include-book "../toplevel")

(b* (((er (list (cons static-env ast))) (acl2::read-file (@ :fname) state))
     (state (f-put-global ':static-env static-env state))
     (state (f-put-global ':ast ast state)))
  (value :ok))


(defconst *magic-delimiter* "!@#$%^%$#@")

(time$
 (b* ((- (cw "~%~s0 begin ASL interpreter output~%" *magic-delimiter*))
      (result (run (@ :static-env) (@ :ast))))
   (eval_result-case result
     :ev_error (cw "Error: ~s0 -- ~x1~%" result.desc result.data)
     :ev_throwing (cw "Uncaught exception: ~x0~%" result.throwdata)
     :ev_normal (val-case result.res
                  :v_int (and (not (eql result.res.val 0))
                              (cw "status: ~x0" result.res.val))
                  :otherwise (cw "bad return value from main: ~x0" result.res)))
   (cw "~%~s0 end ASL interpreter output~%" *magic-delimiter*))
 :msg "ASL run: ~st sec, ~sa bytes.~%")

