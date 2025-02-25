

;; (assign :fname "ilog2-ast.lsp")

(in-package "ASL")

(include-book "../interp")

(b* (((er (list (cons static-env ast))) (acl2::read-file (@ :fname) state))
     (state (f-put-global ':static-env static-env state))
     (state (f-put-global ':ast ast state)))
  (value :ok))


(b* ((env (make-env :global (make-global-env :static (@ :static-env))
                    :local (empty-local-env)))
     (result (time$ (eval_subprogram env "main" nil nil :clk 1000000))))
  (eval_result-case result
    :ev_error (er hard? 'run-asl-test "Error: ~s0 -- ~x1~%" result.desc result.data)
    :ev_throwing (er hard? 'run-asl-test "Uncaught exception: ~x0~%" result.throwdata)
    :ev_normal (b* (((func_result res) result.res))
                 res.vals)))
