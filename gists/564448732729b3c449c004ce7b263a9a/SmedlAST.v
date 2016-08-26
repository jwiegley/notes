      def monitor "foo" {{
        state: {
          var "nat" := "currentTime"
        }
        events: {
          imported "getTime" := ("nat")
        }
        scenarios: {
          def scenario "push" := {
            "Start" ~~~>
              do step: "getTime" := ("ttime")
                          when ^"ttime" >= ^"currentTime"
                        then { ^"currentTime" = ^"ttime" };
                 step: "null" := () when (#1 == #2);
              ~> "Start"
              else { raise "Failure" } ~> "Finish"
          }%traces;

          def scenario "pop" := {
            "Start" ~~~>
              do step: "null" := () when (#1 == #2)
                       then { raise "Failure" };
                 step: "null" := () when (#1 == #2);
              ~> "Start"
              else { raise "Failure" } ~> "Finish"
          }%traces
        }
      }}
