(assert (let ((a!1 (+ start10!55
              (ite (= choice!10 1)
                   3
                   (ite (= choice!10 0)
                        1
                        (select m_store-basic_latency!32 choice!10))))))
  (<= a!1 22)))
