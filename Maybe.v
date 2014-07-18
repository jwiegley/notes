  repeat (match goal with
    | [ |- match ?X with _ => _ end = ?X ] => destruct X; auto
    | [ |- ?X = match ?X with _ => _ end ] => destruct X; auto
    | [ |- match ?X with _ => _ end =
           match ?X with _ => _ end ] => destruct X; auto
    | [ |- ?X = match match ?X with _ => _ end
             with _ => _ end ] => destruct X; auto
    | [ |- match match ?X with _ => _ end
             with _ => _ end = ?X ] => destruct X; auto
    | [ |- match match ?X with _ => _ end with _ => _ end =
           match ?X with _ => _ end ] => destruct X; auto
    | [ |- match ?X with _ => _ end =
           match match ?X with _ => _ end
             with _ => _ end ] => destruct X; auto
    | [ |- match match ?X with _ => _ end with _ => _ end =
           match match ?X with _ => _ end
             with _ => _ end ] => destruct X; auto
    | [ |- match match ?X with _ => _ end
             with _ => _ end =
           match match ?X with _ => _ end
             with _ => _ end ] => destruct X; auto
    | [ |- match match match ?X with _ => _ end
             with _ => _ end with _ => _ end =
           match ?X with _ => _ end ] => destruct X; auto
    end);
