/* run.config*
MODULE: Debug_category
EXIT: 0
  OPT: -test-msg-key help -test-warn-key="a=inactive"
  OPT: -test-msg-key a -test-warn-key="a=inactive"
  OPT: -test-msg-key a -test-msg-key="-a:b" -test-warn-key="a=inactive"
  OPT: -test-msg-key a -test-msg-key="-a:b" -test-msg-key a:b:c -test-warn-key="a=inactive"
  OPT: -test-msg-key "a:b:c,d" -test-warn-key="a=inactive"
  OPT: -test-msg-key "*" -test-warn-key="a=inactive"
  OPT:
EXIT: 1
  OPT: -test-warn-key a=error
  OPT: -test-warn-key a=abort
EXIT: 0
  OPT: -test-warn-key a=feedback
EXIT: 1
  OPT: -test-warn-key="*=abort"
EXIT: 0
  OPT: -test-warn-key=a=once
  OPT: -test-warn-key a=feedback-once
EXIT: 1
  OPT: -test-warn-key a=err-once
  OPT: -test-warn-key test-vis-err
  OPT: -test-warn-key test-inv-err
EXIT: 4
  OPT: -test-warn-key test-failure
FILTER: sed 's|Your Frama-C version is.*|Your Frama-C version is VERSION|'
*/
