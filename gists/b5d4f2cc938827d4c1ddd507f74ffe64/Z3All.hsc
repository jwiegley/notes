{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#include <bindings.dsl.h>
#include "z3_all.h"
module .Z3Z3All where
import Foreign.Ptr
#strict_import

{- typedef signed char __int8_t; -}
#synonym_t __int8_t , CSChar
{- typedef unsigned char __uint8_t; -}
#synonym_t __uint8_t , CUChar
{- typedef short __int16_t; -}
#synonym_t __int16_t , CShort
{- typedef unsigned short __uint16_t; -}
#synonym_t __uint16_t , CUShort
{- typedef int __int32_t; -}
#synonym_t __int32_t , CInt
{- typedef unsigned int __uint32_t; -}
#synonym_t __uint32_t , CUInt
{- typedef long long __int64_t; -}
#synonym_t __int64_t , CLong
{- typedef unsigned long long __uint64_t; -}
#synonym_t __uint64_t , CULong
{- typedef long __darwin_intptr_t; -}
#synonym_t __darwin_intptr_t , CLong
{- typedef unsigned int __darwin_natural_t; -}
#synonym_t __darwin_natural_t , CUInt
{- typedef int __darwin_ct_rune_t; -}
#synonym_t __darwin_ct_rune_t , CInt
{- typedef union {
            char __mbstate8[128]; long long _mbstateL;
        } __mbstate_t; -}
#starttype __mbstate_t
#array_field __mbstate8 , CChar
#field _mbstateL , CLong
#stoptype
{- typedef __mbstate_t __darwin_mbstate_t; -}
#synonym_t __darwin_mbstate_t , <__mbstate_t>
{- typedef long int __darwin_ptrdiff_t; -}
#synonym_t __darwin_ptrdiff_t , CLong
{- typedef long unsigned int __darwin_size_t; -}
#synonym_t __darwin_size_t , CLong
{- typedef __builtin_va_list __darwin_va_list; -}
#synonym_t __darwin_va_list , <__builtin_va_list>
{- typedef int __darwin_wchar_t; -}
#synonym_t __darwin_wchar_t , CInt
{- typedef __darwin_wchar_t __darwin_rune_t; -}
#synonym_t __darwin_rune_t , CInt
{- typedef int __darwin_wint_t; -}
#synonym_t __darwin_wint_t , CInt
{- typedef unsigned long __darwin_clock_t; -}
#synonym_t __darwin_clock_t , CULong
{- typedef __uint32_t __darwin_socklen_t; -}
#synonym_t __darwin_socklen_t , CUInt
{- typedef long __darwin_ssize_t; -}
#synonym_t __darwin_ssize_t , CLong
{- typedef long __darwin_time_t; -}
#synonym_t __darwin_time_t , CLong
{- typedef __int64_t __darwin_blkcnt_t; -}
#synonym_t __darwin_blkcnt_t , CLong
{- typedef __int32_t __darwin_blksize_t; -}
#synonym_t __darwin_blksize_t , CInt
{- typedef __int32_t __darwin_dev_t; -}
#synonym_t __darwin_dev_t , CInt
{- typedef unsigned int __darwin_fsblkcnt_t; -}
#synonym_t __darwin_fsblkcnt_t , CUInt
{- typedef unsigned int __darwin_fsfilcnt_t; -}
#synonym_t __darwin_fsfilcnt_t , CUInt
{- typedef __uint32_t __darwin_gid_t; -}
#synonym_t __darwin_gid_t , CUInt
{- typedef __uint32_t __darwin_id_t; -}
#synonym_t __darwin_id_t , CUInt
{- typedef __uint64_t __darwin_ino64_t; -}
#synonym_t __darwin_ino64_t , CULong
{- typedef __darwin_ino64_t __darwin_ino_t; -}
#synonym_t __darwin_ino_t , CULong
{- typedef __darwin_natural_t __darwin_mach_port_name_t; -}
#synonym_t __darwin_mach_port_name_t , CUInt
{- typedef __darwin_mach_port_name_t __darwin_mach_port_t; -}
#synonym_t __darwin_mach_port_t , CUInt
{- typedef __uint16_t __darwin_mode_t; -}
#synonym_t __darwin_mode_t , CUShort
{- typedef __int64_t __darwin_off_t; -}
#synonym_t __darwin_off_t , CLong
{- typedef __int32_t __darwin_pid_t; -}
#synonym_t __darwin_pid_t , CInt
{- typedef __uint32_t __darwin_sigset_t; -}
#synonym_t __darwin_sigset_t , CUInt
{- typedef __int32_t __darwin_suseconds_t; -}
#synonym_t __darwin_suseconds_t , CInt
{- typedef __uint32_t __darwin_uid_t; -}
#synonym_t __darwin_uid_t , CUInt
{- typedef __uint32_t __darwin_useconds_t; -}
#synonym_t __darwin_useconds_t , CUInt
#globalarray __darwin_uuid_t , CUChar
#globalarray __darwin_uuid_string_t , CChar
{- struct __darwin_pthread_handler_rec {
    void (* __routine)(void *);
    void * __arg;
    struct __darwin_pthread_handler_rec * __next;
}; -}
#starttype struct __darwin_pthread_handler_rec
#field __routine , FunPtr (Ptr () -> IO ())
#field __arg , Ptr ()
#field __next , Ptr <struct __darwin_pthread_handler_rec>
#stoptype
{- struct _opaque_pthread_attr_t {
    long __sig; char __opaque[56];
}; -}
#starttype struct _opaque_pthread_attr_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_cond_t {
    long __sig; char __opaque[40];
}; -}
#starttype struct _opaque_pthread_cond_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_condattr_t {
    long __sig; char __opaque[8];
}; -}
#starttype struct _opaque_pthread_condattr_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_mutex_t {
    long __sig; char __opaque[56];
}; -}
#starttype struct _opaque_pthread_mutex_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_mutexattr_t {
    long __sig; char __opaque[8];
}; -}
#starttype struct _opaque_pthread_mutexattr_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_once_t {
    long __sig; char __opaque[8];
}; -}
#starttype struct _opaque_pthread_once_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_rwlock_t {
    long __sig; char __opaque[192];
}; -}
#starttype struct _opaque_pthread_rwlock_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_rwlockattr_t {
    long __sig; char __opaque[16];
}; -}
#starttype struct _opaque_pthread_rwlockattr_t
#field __sig , CLong
#array_field __opaque , CChar
#stoptype
{- struct _opaque_pthread_t {
    long __sig;
    struct __darwin_pthread_handler_rec * __cleanup_stack;
    char __opaque[8176];
}; -}
#starttype struct _opaque_pthread_t
#field __sig , CLong
#field __cleanup_stack , Ptr <struct __darwin_pthread_handler_rec>
#array_field __opaque , CChar
#stoptype
{- typedef struct _opaque_pthread_attr_t __darwin_pthread_attr_t; -}
#opaque_t struct _opaque_pthread_attr_t
#synonym_t __darwin_pthread_attr_t , <struct _opaque_pthread_attr_t>
{- typedef struct _opaque_pthread_cond_t __darwin_pthread_cond_t; -}
#opaque_t struct _opaque_pthread_cond_t
#synonym_t __darwin_pthread_cond_t , <struct _opaque_pthread_cond_t>
{- typedef struct _opaque_pthread_condattr_t __darwin_pthread_condattr_t; -}
#opaque_t struct _opaque_pthread_condattr_t
#synonym_t __darwin_pthread_condattr_t , <struct _opaque_pthread_condattr_t>
{- typedef unsigned long __darwin_pthread_key_t; -}
#synonym_t __darwin_pthread_key_t , CULong
{- typedef struct _opaque_pthread_mutex_t __darwin_pthread_mutex_t; -}
#opaque_t struct _opaque_pthread_mutex_t
#synonym_t __darwin_pthread_mutex_t , <struct _opaque_pthread_mutex_t>
{- typedef struct _opaque_pthread_mutexattr_t __darwin_pthread_mutexattr_t; -}
#opaque_t struct _opaque_pthread_mutexattr_t
#synonym_t __darwin_pthread_mutexattr_t , <struct _opaque_pthread_mutexattr_t>
{- typedef struct _opaque_pthread_once_t __darwin_pthread_once_t; -}
#opaque_t struct _opaque_pthread_once_t
#synonym_t __darwin_pthread_once_t , <struct _opaque_pthread_once_t>
{- typedef struct _opaque_pthread_rwlock_t __darwin_pthread_rwlock_t; -}
#opaque_t struct _opaque_pthread_rwlock_t
#synonym_t __darwin_pthread_rwlock_t , <struct _opaque_pthread_rwlock_t>
{- typedef struct _opaque_pthread_rwlockattr_t __darwin_pthread_rwlockattr_t; -}
#opaque_t struct _opaque_pthread_rwlockattr_t
#synonym_t __darwin_pthread_rwlockattr_t , <struct _opaque_pthread_rwlockattr_t>
#globalvar __darwin_pthread_t , Ptr (<struct _opaque_pthread_t>)
{- typedef int __darwin_nl_item; -}
#synonym_t __darwin_nl_item , CInt
{- typedef int __darwin_wctrans_t; -}
#synonym_t __darwin_wctrans_t , CInt
{- typedef __uint32_t __darwin_wctype_t; -}
#synonym_t __darwin_wctype_t , CUInt
{- typedef __darwin_va_list va_list; -}
#synonym_t va_list , <__builtin_va_list>
{- typedef __darwin_size_t size_t; -}
#synonym_t size_t , CLong
#ccall renameat , CInt -> CString -> CInt -> CString -> IO CInt
{- typedef __darwin_off_t fpos_t; -}
#synonym_t fpos_t , CLong
{- struct __sbuf {
    unsigned char * _base; int _size;
}; -}
#starttype struct __sbuf
#field _base , Ptr CUChar
#field _size , CInt
#stoptype
{- struct __sFILEX; -}
#opaque_t struct __sFILEX
{- typedef struct __sFILE {
            unsigned char * _p;
            int _r;
            int _w;
            short _flags;
            short _file;
            struct __sbuf _bf;
            int _lbfsize;
            void * _cookie;
            int (* _close)(void *);
            int (* _read)(void *, char *, int);
            fpos_t (* _seek)(void *, fpos_t, int);
            int (* _write)(void *, const char *, int);
            struct __sbuf _ub;
            struct __sFILEX * _extra;
            int _ur;
            unsigned char _ubuf[3];
            unsigned char _nbuf[1];
            struct __sbuf _lb;
            int _blksize;
            fpos_t _offset;
        } FILE; -}
#starttype struct __sFILE
#field _p , Ptr CUChar
#field _r , CInt
#field _w , CInt
#field _flags , CShort
#field _file , CShort
#field _bf , <struct __sbuf>
#field _lbfsize , CInt
#field _cookie , Ptr ()
#field _close , FunPtr (Ptr () -> CInt)
#field _read , FunPtr (Ptr () -> CString -> CInt -> CInt)
#field _seek , FunPtr (Ptr () -> CLong -> CInt -> CLong)
#field _write , FunPtr (Ptr () -> CString -> CInt -> CInt)
#field _ub , <struct __sbuf>
#field _extra , Ptr <struct __sFILEX>
#field _ur , CInt
#array_field _ubuf , CUChar
#array_field _nbuf , CUChar
#field _lb , <struct __sbuf>
#field _blksize , CInt
#field _offset , CLong
#stoptype
#synonym_t FILE , <struct __sFILE>
#globalvar __stdinp , Ptr (<struct __sFILE>)
#globalvar __stdoutp , Ptr (<struct __sFILE>)
#globalvar __stderrp , Ptr (<struct __sFILE>)
#ccall clearerr , Ptr <struct __sFILE> -> IO ()
#ccall fclose , Ptr <struct __sFILE> -> IO CInt
#ccall feof , Ptr <struct __sFILE> -> IO CInt
#ccall ferror , Ptr <struct __sFILE> -> IO CInt
#ccall fflush , Ptr <struct __sFILE> -> IO CInt
#ccall fgetc , Ptr <struct __sFILE> -> IO CInt
#ccall fgetpos , Ptr <struct __sFILE> -> Ptr CLong -> IO CInt
#ccall fgets , CString -> CInt -> Ptr <struct __sFILE> -> IO CString
#ccall fopen , CString -> CString -> IO (Ptr <struct __sFILE>)
#ccall fprintf , Ptr <struct __sFILE> -> CString -> IO CInt
#ccall fputc , CInt -> Ptr <struct __sFILE> -> IO CInt
#ccall fputs , CString -> Ptr <struct __sFILE> -> IO CInt
#ccall fread , Ptr () -> CSize -> CSize -> Ptr <struct __sFILE> -> IO CSize
#ccall freopen , CString -> CString -> Ptr <struct __sFILE> -> IO (Ptr <struct __sFILE>)
#ccall fscanf , Ptr <struct __sFILE> -> CString -> IO CInt
#ccall fseek , Ptr <struct __sFILE> -> CLong -> CInt -> IO CInt
#ccall fsetpos , Ptr <struct __sFILE> -> Ptr CLong -> IO CInt
#ccall ftell , Ptr <struct __sFILE> -> IO CLong
#ccall fwrite , Ptr () -> CSize -> CSize -> Ptr <struct __sFILE> -> IO CSize
#ccall getc , Ptr <struct __sFILE> -> IO CInt
#ccall getchar , IO CInt
#ccall gets , CString -> IO CString
#ccall perror , CString -> IO ()
#ccall printf , CString -> IO CInt
#ccall putc , CInt -> Ptr <struct __sFILE> -> IO CInt
#ccall putchar , CInt -> IO CInt
#ccall puts , CString -> IO CInt
#ccall remove , CString -> IO CInt
#ccall rename , CString -> CString -> IO CInt
#ccall rewind , Ptr <struct __sFILE> -> IO ()
#ccall scanf , CString -> IO CInt
#ccall setbuf , Ptr <struct __sFILE> -> CString -> IO ()
#ccall setvbuf , Ptr <struct __sFILE> -> CString -> CInt -> CSize -> IO CInt
#ccall sprintf , CString -> CString -> IO CInt
#ccall sscanf , CString -> CString -> IO CInt
#ccall tmpfile , IO (Ptr <struct __sFILE>)
#ccall tmpnam , CString -> IO CString
#ccall ungetc , CInt -> Ptr <struct __sFILE> -> IO CInt
#ccall vfprintf , Ptr <struct __sFILE> -> CString -> <__builtin_va_list> -> IO CInt
#ccall vprintf , CString -> <__builtin_va_list> -> IO CInt
#ccall vsprintf , CString -> CString -> <__builtin_va_list> -> IO CInt
#ccall ctermid , CString -> IO CString
#ccall fdopen , CInt -> CString -> IO (Ptr <struct __sFILE>)
#ccall fileno , Ptr <struct __sFILE> -> IO CInt
#ccall pclose , Ptr <struct __sFILE> -> IO CInt
#ccall popen , CString -> CString -> IO (Ptr <struct __sFILE>)
#ccall __srget , Ptr <struct __sFILE> -> IO CInt
#ccall __svfscanf , Ptr <struct __sFILE> -> CString -> <__builtin_va_list> -> IO CInt
#ccall __swbuf , CInt -> Ptr <struct __sFILE> -> IO CInt
#cinline __sputc , CInt -> Ptr <struct __sFILE> -> IO CInt
#ccall flockfile , Ptr <struct __sFILE> -> IO ()
#ccall ftrylockfile , Ptr <struct __sFILE> -> IO CInt
#ccall funlockfile , Ptr <struct __sFILE> -> IO ()
#ccall getc_unlocked , Ptr <struct __sFILE> -> IO CInt
#ccall getchar_unlocked , IO CInt
#ccall putc_unlocked , CInt -> Ptr <struct __sFILE> -> IO CInt
#ccall putchar_unlocked , CInt -> IO CInt
#ccall getw , Ptr <struct __sFILE> -> IO CInt
#ccall putw , CInt -> Ptr <struct __sFILE> -> IO CInt
#ccall tempnam , CString -> CString -> IO CString
{- typedef __darwin_off_t off_t; -}
#synonym_t off_t , CLong
#ccall fseeko , Ptr <struct __sFILE> -> CLong -> CInt -> IO CInt
#ccall ftello , Ptr <struct __sFILE> -> IO CLong
#ccall snprintf , CString -> CSize -> CString -> IO CInt
#ccall vfscanf , Ptr <struct __sFILE> -> CString -> <__builtin_va_list> -> IO CInt
#ccall vscanf , CString -> <__builtin_va_list> -> IO CInt
#ccall vsnprintf , CString -> CSize -> CString -> <__builtin_va_list> -> IO CInt
#ccall vsscanf , CString -> CString -> <__builtin_va_list> -> IO CInt
{- typedef __darwin_ssize_t ssize_t; -}
#synonym_t ssize_t , CLong
#ccall dprintf , CInt -> CString -> IO CInt
#ccall vdprintf , CInt -> CString -> <__builtin_va_list> -> IO CInt
#ccall getdelim , Ptr CString -> Ptr CSize -> CInt -> Ptr <struct __sFILE> -> IO CLong
#ccall getline , Ptr CString -> Ptr CSize -> Ptr <struct __sFILE> -> IO CLong
#globalvar sys_nerr , CInt
#globalarray sys_errlist , Ptr CChar
#ccall asprintf , Ptr CString -> CString -> IO CInt
#ccall ctermid_r , CString -> IO CString
#ccall fgetln , Ptr <struct __sFILE> -> Ptr CSize -> IO CString
#ccall fmtcheck , CString -> CString -> IO CString
#ccall fpurge , Ptr <struct __sFILE> -> IO CInt
#ccall setbuffer , Ptr <struct __sFILE> -> CString -> CInt -> IO ()
#ccall setlinebuf , Ptr <struct __sFILE> -> IO CInt
#ccall vasprintf , Ptr CString -> CString -> <__builtin_va_list> -> IO CInt
#ccall zopen , CString -> CString -> CInt -> IO (Ptr <struct __sFILE>)
#ccall funopen , Ptr () -> FunPtr (Ptr () -> CString -> CInt -> CInt) -> FunPtr (Ptr () -> CString -> CInt -> CInt) -> FunPtr (Ptr () -> CLong -> CInt -> CLong) -> FunPtr (Ptr () -> CInt) -> IO (Ptr <struct __sFILE>)
#ccall __sprintf_chk , CString -> CInt -> CSize -> CString -> IO CInt
#ccall __snprintf_chk , CString -> CSize -> CInt -> CSize -> CString -> IO CInt
#ccall __vsprintf_chk , CString -> CInt -> CSize -> CString -> <__builtin_va_list> -> IO CInt
#ccall __vsnprintf_chk , CString -> CSize -> CInt -> CSize -> CString -> <__builtin_va_list> -> IO CInt
#globalvar Z3_symbol , Ptr (<struct _Z3_symbol>)
#globalvar Z3_literals , Ptr (<struct _Z3_literals>)
#globalvar Z3_config , Ptr (<struct _Z3_config>)
#globalvar Z3_context , Ptr (<struct _Z3_context>)
#globalvar Z3_sort , Ptr (<struct _Z3_sort>)
#globalvar Z3_func_decl , Ptr (<struct _Z3_func_decl>)
#globalvar Z3_ast , Ptr (<struct _Z3_ast>)
#globalvar Z3_app , Ptr (<struct _Z3_app>)
#globalvar Z3_pattern , Ptr (<struct _Z3_pattern>)
#globalvar Z3_model , Ptr (<struct _Z3_model>)
#globalvar Z3_constructor , Ptr (<struct _Z3_constructor>)
#globalvar Z3_constructor_list , Ptr (<struct _Z3_constructor_list>)
#globalvar Z3_params , Ptr (<struct _Z3_params>)
#globalvar Z3_param_descrs , Ptr (<struct _Z3_param_descrs>)
#globalvar Z3_goal , Ptr (<struct _Z3_goal>)
#globalvar Z3_tactic , Ptr (<struct _Z3_tactic>)
#globalvar Z3_probe , Ptr (<struct _Z3_probe>)
#globalvar Z3_stats , Ptr (<struct _Z3_stats>)
#globalvar Z3_solver , Ptr (<struct _Z3_solver>)
#globalvar Z3_ast_vector , Ptr (<struct _Z3_ast_vector>)
#globalvar Z3_ast_map , Ptr (<struct _Z3_ast_map>)
#globalvar Z3_apply_result , Ptr (<struct _Z3_apply_result>)
#globalvar Z3_func_interp , Ptr (<struct _Z3_func_interp>)
#globalvar Z3_func_entry , Ptr (<struct _Z3_func_entry>)
#globalvar Z3_fixedpoint , Ptr (<struct _Z3_fixedpoint>)
#globalvar Z3_optimize , Ptr (<struct _Z3_optimize>)
#globalvar Z3_rcf_num , Ptr (<struct _Z3_rcf_num>)
{- typedef int Z3_bool; -}
#synonym_t Z3_bool , CInt
#globalvar Z3_string , Ptr CChar
#globalvar Z3_string_ptr , Ptr <Z3_string>
{- typedef enum {
            Z3_L_FALSE = -1, Z3_L_UNDEF, Z3_L_TRUE
        } Z3_lbool; -}
#integral_t Z3_lbool
#num Z3_L_FALSE
#num Z3_L_UNDEF
#num Z3_L_TRUE
{- typedef enum {
            Z3_INT_SYMBOL, Z3_STRING_SYMBOL
        } Z3_symbol_kind; -}
#integral_t Z3_symbol_kind
#num Z3_INT_SYMBOL
#num Z3_STRING_SYMBOL
{- typedef enum {
            Z3_PARAMETER_INT,
            Z3_PARAMETER_DOUBLE,
            Z3_PARAMETER_RATIONAL,
            Z3_PARAMETER_SYMBOL,
            Z3_PARAMETER_SORT,
            Z3_PARAMETER_AST,
            Z3_PARAMETER_FUNC_DECL
        } Z3_parameter_kind; -}
#integral_t Z3_parameter_kind
#num Z3_PARAMETER_INT
#num Z3_PARAMETER_DOUBLE
#num Z3_PARAMETER_RATIONAL
#num Z3_PARAMETER_SYMBOL
#num Z3_PARAMETER_SORT
#num Z3_PARAMETER_AST
#num Z3_PARAMETER_FUNC_DECL
{- typedef enum {
            Z3_UNINTERPRETED_SORT,
            Z3_BOOL_SORT,
            Z3_INT_SORT,
            Z3_REAL_SORT,
            Z3_BV_SORT,
            Z3_ARRAY_SORT,
            Z3_DATATYPE_SORT,
            Z3_RELATION_SORT,
            Z3_FINITE_DOMAIN_SORT,
            Z3_FLOATING_POINT_SORT,
            Z3_ROUNDING_MODE_SORT,
            Z3_SEQ_SORT,
            Z3_RE_SORT,
            Z3_UNKNOWN_SORT = 1000
        } Z3_sort_kind; -}
#integral_t Z3_sort_kind
#num Z3_UNINTERPRETED_SORT
#num Z3_BOOL_SORT
#num Z3_INT_SORT
#num Z3_REAL_SORT
#num Z3_BV_SORT
#num Z3_ARRAY_SORT
#num Z3_DATATYPE_SORT
#num Z3_RELATION_SORT
#num Z3_FINITE_DOMAIN_SORT
#num Z3_FLOATING_POINT_SORT
#num Z3_ROUNDING_MODE_SORT
#num Z3_SEQ_SORT
#num Z3_RE_SORT
#num Z3_UNKNOWN_SORT
{- typedef enum {
            Z3_NUMERAL_AST,
            Z3_APP_AST,
            Z3_VAR_AST,
            Z3_QUANTIFIER_AST,
            Z3_SORT_AST,
            Z3_FUNC_DECL_AST,
            Z3_UNKNOWN_AST = 1000
        } Z3_ast_kind; -}
#integral_t Z3_ast_kind
#num Z3_NUMERAL_AST
#num Z3_APP_AST
#num Z3_VAR_AST
#num Z3_QUANTIFIER_AST
#num Z3_SORT_AST
#num Z3_FUNC_DECL_AST
#num Z3_UNKNOWN_AST
{- typedef enum {
            Z3_OP_TRUE = 0x100,
            Z3_OP_FALSE,
            Z3_OP_EQ,
            Z3_OP_DISTINCT,
            Z3_OP_ITE,
            Z3_OP_AND,
            Z3_OP_OR,
            Z3_OP_IFF,
            Z3_OP_XOR,
            Z3_OP_NOT,
            Z3_OP_IMPLIES,
            Z3_OP_OEQ,
            Z3_OP_INTERP,
            Z3_OP_ANUM = 0x200,
            Z3_OP_AGNUM,
            Z3_OP_LE,
            Z3_OP_GE,
            Z3_OP_LT,
            Z3_OP_GT,
            Z3_OP_ADD,
            Z3_OP_SUB,
            Z3_OP_UMINUS,
            Z3_OP_MUL,
            Z3_OP_DIV,
            Z3_OP_IDIV,
            Z3_OP_REM,
            Z3_OP_MOD,
            Z3_OP_TO_REAL,
            Z3_OP_TO_INT,
            Z3_OP_IS_INT,
            Z3_OP_POWER,
            Z3_OP_STORE = 0x300,
            Z3_OP_SELECT,
            Z3_OP_CONST_ARRAY,
            Z3_OP_ARRAY_MAP,
            Z3_OP_ARRAY_DEFAULT,
            Z3_OP_SET_UNION,
            Z3_OP_SET_INTERSECT,
            Z3_OP_SET_DIFFERENCE,
            Z3_OP_SET_COMPLEMENT,
            Z3_OP_SET_SUBSET,
            Z3_OP_AS_ARRAY,
            Z3_OP_ARRAY_EXT,
            Z3_OP_BNUM = 0x400,
            Z3_OP_BIT1,
            Z3_OP_BIT0,
            Z3_OP_BNEG,
            Z3_OP_BADD,
            Z3_OP_BSUB,
            Z3_OP_BMUL,
            Z3_OP_BSDIV,
            Z3_OP_BUDIV,
            Z3_OP_BSREM,
            Z3_OP_BUREM,
            Z3_OP_BSMOD,
            Z3_OP_BSDIV0,
            Z3_OP_BUDIV0,
            Z3_OP_BSREM0,
            Z3_OP_BUREM0,
            Z3_OP_BSMOD0,
            Z3_OP_ULEQ,
            Z3_OP_SLEQ,
            Z3_OP_UGEQ,
            Z3_OP_SGEQ,
            Z3_OP_ULT,
            Z3_OP_SLT,
            Z3_OP_UGT,
            Z3_OP_SGT,
            Z3_OP_BAND,
            Z3_OP_BOR,
            Z3_OP_BNOT,
            Z3_OP_BXOR,
            Z3_OP_BNAND,
            Z3_OP_BNOR,
            Z3_OP_BXNOR,
            Z3_OP_CONCAT,
            Z3_OP_SIGN_EXT,
            Z3_OP_ZERO_EXT,
            Z3_OP_EXTRACT,
            Z3_OP_REPEAT,
            Z3_OP_BREDOR,
            Z3_OP_BREDAND,
            Z3_OP_BCOMP,
            Z3_OP_BSHL,
            Z3_OP_BLSHR,
            Z3_OP_BASHR,
            Z3_OP_ROTATE_LEFT,
            Z3_OP_ROTATE_RIGHT,
            Z3_OP_EXT_ROTATE_LEFT,
            Z3_OP_EXT_ROTATE_RIGHT,
            Z3_OP_BIT2BOOL,
            Z3_OP_INT2BV,
            Z3_OP_BV2INT,
            Z3_OP_CARRY,
            Z3_OP_XOR3,
            Z3_OP_BSMUL_NO_OVFL,
            Z3_OP_BUMUL_NO_OVFL,
            Z3_OP_BSMUL_NO_UDFL,
            Z3_OP_BSDIV_I,
            Z3_OP_BUDIV_I,
            Z3_OP_BSREM_I,
            Z3_OP_BUREM_I,
            Z3_OP_BSMOD_I,
            Z3_OP_PR_UNDEF = 0x500,
            Z3_OP_PR_TRUE,
            Z3_OP_PR_ASSERTED,
            Z3_OP_PR_GOAL,
            Z3_OP_PR_MODUS_PONENS,
            Z3_OP_PR_REFLEXIVITY,
            Z3_OP_PR_SYMMETRY,
            Z3_OP_PR_TRANSITIVITY,
            Z3_OP_PR_TRANSITIVITY_STAR,
            Z3_OP_PR_MONOTONICITY,
            Z3_OP_PR_QUANT_INTRO,
            Z3_OP_PR_DISTRIBUTIVITY,
            Z3_OP_PR_AND_ELIM,
            Z3_OP_PR_NOT_OR_ELIM,
            Z3_OP_PR_REWRITE,
            Z3_OP_PR_REWRITE_STAR,
            Z3_OP_PR_PULL_QUANT,
            Z3_OP_PR_PULL_QUANT_STAR,
            Z3_OP_PR_PUSH_QUANT,
            Z3_OP_PR_ELIM_UNUSED_VARS,
            Z3_OP_PR_DER,
            Z3_OP_PR_QUANT_INST,
            Z3_OP_PR_HYPOTHESIS,
            Z3_OP_PR_LEMMA,
            Z3_OP_PR_UNIT_RESOLUTION,
            Z3_OP_PR_IFF_TRUE,
            Z3_OP_PR_IFF_FALSE,
            Z3_OP_PR_COMMUTATIVITY,
            Z3_OP_PR_DEF_AXIOM,
            Z3_OP_PR_DEF_INTRO,
            Z3_OP_PR_APPLY_DEF,
            Z3_OP_PR_IFF_OEQ,
            Z3_OP_PR_NNF_POS,
            Z3_OP_PR_NNF_NEG,
            Z3_OP_PR_NNF_STAR,
            Z3_OP_PR_CNF_STAR,
            Z3_OP_PR_SKOLEMIZE,
            Z3_OP_PR_MODUS_PONENS_OEQ,
            Z3_OP_PR_TH_LEMMA,
            Z3_OP_PR_HYPER_RESOLVE,
            Z3_OP_RA_STORE = 0x600,
            Z3_OP_RA_EMPTY,
            Z3_OP_RA_IS_EMPTY,
            Z3_OP_RA_JOIN,
            Z3_OP_RA_UNION,
            Z3_OP_RA_WIDEN,
            Z3_OP_RA_PROJECT,
            Z3_OP_RA_FILTER,
            Z3_OP_RA_NEGATION_FILTER,
            Z3_OP_RA_RENAME,
            Z3_OP_RA_COMPLEMENT,
            Z3_OP_RA_SELECT,
            Z3_OP_RA_CLONE,
            Z3_OP_FD_CONSTANT,
            Z3_OP_FD_LT,
            Z3_OP_SEQ_UNIT,
            Z3_OP_SEQ_EMPTY,
            Z3_OP_SEQ_CONCAT,
            Z3_OP_SEQ_PREFIX,
            Z3_OP_SEQ_SUFFIX,
            Z3_OP_SEQ_CONTAINS,
            Z3_OP_SEQ_EXTRACT,
            Z3_OP_SEQ_REPLACE,
            Z3_OP_SEQ_AT,
            Z3_OP_SEQ_LENGTH,
            Z3_OP_SEQ_INDEX,
            Z3_OP_SEQ_TO_RE,
            Z3_OP_SEQ_IN_RE,
            Z3_OP_STR_TO_INT,
            Z3_OP_INT_TO_STR,
            Z3_OP_RE_PLUS,
            Z3_OP_RE_STAR,
            Z3_OP_RE_OPTION,
            Z3_OP_RE_CONCAT,
            Z3_OP_RE_UNION,
            Z3_OP_RE_RANGE,
            Z3_OP_RE_LOOP,
            Z3_OP_RE_INTERSECT,
            Z3_OP_RE_EMPTY_SET,
            Z3_OP_RE_FULL_SET,
            Z3_OP_RE_COMPLEMENT,
            Z3_OP_LABEL = 0x700,
            Z3_OP_LABEL_LIT,
            Z3_OP_DT_CONSTRUCTOR = 0x800,
            Z3_OP_DT_RECOGNISER,
            Z3_OP_DT_ACCESSOR,
            Z3_OP_DT_UPDATE_FIELD,
            Z3_OP_PB_AT_MOST = 0x900,
            Z3_OP_PB_AT_LEAST,
            Z3_OP_PB_LE,
            Z3_OP_PB_GE,
            Z3_OP_PB_EQ,
            Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN,
            Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
            Z3_OP_FPA_RM_TOWARD_POSITIVE,
            Z3_OP_FPA_RM_TOWARD_NEGATIVE,
            Z3_OP_FPA_RM_TOWARD_ZERO,
            Z3_OP_FPA_NUM,
            Z3_OP_FPA_PLUS_INF,
            Z3_OP_FPA_MINUS_INF,
            Z3_OP_FPA_NAN,
            Z3_OP_FPA_PLUS_ZERO,
            Z3_OP_FPA_MINUS_ZERO,
            Z3_OP_FPA_ADD,
            Z3_OP_FPA_SUB,
            Z3_OP_FPA_NEG,
            Z3_OP_FPA_MUL,
            Z3_OP_FPA_DIV,
            Z3_OP_FPA_REM,
            Z3_OP_FPA_ABS,
            Z3_OP_FPA_MIN,
            Z3_OP_FPA_MAX,
            Z3_OP_FPA_FMA,
            Z3_OP_FPA_SQRT,
            Z3_OP_FPA_ROUND_TO_INTEGRAL,
            Z3_OP_FPA_EQ,
            Z3_OP_FPA_LT,
            Z3_OP_FPA_GT,
            Z3_OP_FPA_LE,
            Z3_OP_FPA_GE,
            Z3_OP_FPA_IS_NAN,
            Z3_OP_FPA_IS_INF,
            Z3_OP_FPA_IS_ZERO,
            Z3_OP_FPA_IS_NORMAL,
            Z3_OP_FPA_IS_SUBNORMAL,
            Z3_OP_FPA_IS_NEGATIVE,
            Z3_OP_FPA_IS_POSITIVE,
            Z3_OP_FPA_FP,
            Z3_OP_FPA_TO_FP,
            Z3_OP_FPA_TO_FP_UNSIGNED,
            Z3_OP_FPA_TO_UBV,
            Z3_OP_FPA_TO_SBV,
            Z3_OP_FPA_TO_REAL,
            Z3_OP_FPA_TO_IEEE_BV,
            Z3_OP_FPA_BVWRAP,
            Z3_OP_FPA_BV2RM,
            Z3_OP_INTERNAL,
            Z3_OP_UNINTERPRETED
        } Z3_decl_kind; -}
#integral_t Z3_decl_kind
#num Z3_OP_TRUE
#num Z3_OP_FALSE
#num Z3_OP_EQ
#num Z3_OP_DISTINCT
#num Z3_OP_ITE
#num Z3_OP_AND
#num Z3_OP_OR
#num Z3_OP_IFF
#num Z3_OP_XOR
#num Z3_OP_NOT
#num Z3_OP_IMPLIES
#num Z3_OP_OEQ
#num Z3_OP_INTERP
#num Z3_OP_ANUM
#num Z3_OP_AGNUM
#num Z3_OP_LE
#num Z3_OP_GE
#num Z3_OP_LT
#num Z3_OP_GT
#num Z3_OP_ADD
#num Z3_OP_SUB
#num Z3_OP_UMINUS
#num Z3_OP_MUL
#num Z3_OP_DIV
#num Z3_OP_IDIV
#num Z3_OP_REM
#num Z3_OP_MOD
#num Z3_OP_TO_REAL
#num Z3_OP_TO_INT
#num Z3_OP_IS_INT
#num Z3_OP_POWER
#num Z3_OP_STORE
#num Z3_OP_SELECT
#num Z3_OP_CONST_ARRAY
#num Z3_OP_ARRAY_MAP
#num Z3_OP_ARRAY_DEFAULT
#num Z3_OP_SET_UNION
#num Z3_OP_SET_INTERSECT
#num Z3_OP_SET_DIFFERENCE
#num Z3_OP_SET_COMPLEMENT
#num Z3_OP_SET_SUBSET
#num Z3_OP_AS_ARRAY
#num Z3_OP_ARRAY_EXT
#num Z3_OP_BNUM
#num Z3_OP_BIT1
#num Z3_OP_BIT0
#num Z3_OP_BNEG
#num Z3_OP_BADD
#num Z3_OP_BSUB
#num Z3_OP_BMUL
#num Z3_OP_BSDIV
#num Z3_OP_BUDIV
#num Z3_OP_BSREM
#num Z3_OP_BUREM
#num Z3_OP_BSMOD
#num Z3_OP_BSDIV0
#num Z3_OP_BUDIV0
#num Z3_OP_BSREM0
#num Z3_OP_BUREM0
#num Z3_OP_BSMOD0
#num Z3_OP_ULEQ
#num Z3_OP_SLEQ
#num Z3_OP_UGEQ
#num Z3_OP_SGEQ
#num Z3_OP_ULT
#num Z3_OP_SLT
#num Z3_OP_UGT
#num Z3_OP_SGT
#num Z3_OP_BAND
#num Z3_OP_BOR
#num Z3_OP_BNOT
#num Z3_OP_BXOR
#num Z3_OP_BNAND
#num Z3_OP_BNOR
#num Z3_OP_BXNOR
#num Z3_OP_CONCAT
#num Z3_OP_SIGN_EXT
#num Z3_OP_ZERO_EXT
#num Z3_OP_EXTRACT
#num Z3_OP_REPEAT
#num Z3_OP_BREDOR
#num Z3_OP_BREDAND
#num Z3_OP_BCOMP
#num Z3_OP_BSHL
#num Z3_OP_BLSHR
#num Z3_OP_BASHR
#num Z3_OP_ROTATE_LEFT
#num Z3_OP_ROTATE_RIGHT
#num Z3_OP_EXT_ROTATE_LEFT
#num Z3_OP_EXT_ROTATE_RIGHT
#num Z3_OP_BIT2BOOL
#num Z3_OP_INT2BV
#num Z3_OP_BV2INT
#num Z3_OP_CARRY
#num Z3_OP_XOR3
#num Z3_OP_BSMUL_NO_OVFL
#num Z3_OP_BUMUL_NO_OVFL
#num Z3_OP_BSMUL_NO_UDFL
#num Z3_OP_BSDIV_I
#num Z3_OP_BUDIV_I
#num Z3_OP_BSREM_I
#num Z3_OP_BUREM_I
#num Z3_OP_BSMOD_I
#num Z3_OP_PR_UNDEF
#num Z3_OP_PR_TRUE
#num Z3_OP_PR_ASSERTED
#num Z3_OP_PR_GOAL
#num Z3_OP_PR_MODUS_PONENS
#num Z3_OP_PR_REFLEXIVITY
#num Z3_OP_PR_SYMMETRY
#num Z3_OP_PR_TRANSITIVITY
#num Z3_OP_PR_TRANSITIVITY_STAR
#num Z3_OP_PR_MONOTONICITY
#num Z3_OP_PR_QUANT_INTRO
#num Z3_OP_PR_DISTRIBUTIVITY
#num Z3_OP_PR_AND_ELIM
#num Z3_OP_PR_NOT_OR_ELIM
#num Z3_OP_PR_REWRITE
#num Z3_OP_PR_REWRITE_STAR
#num Z3_OP_PR_PULL_QUANT
#num Z3_OP_PR_PULL_QUANT_STAR
#num Z3_OP_PR_PUSH_QUANT
#num Z3_OP_PR_ELIM_UNUSED_VARS
#num Z3_OP_PR_DER
#num Z3_OP_PR_QUANT_INST
#num Z3_OP_PR_HYPOTHESIS
#num Z3_OP_PR_LEMMA
#num Z3_OP_PR_UNIT_RESOLUTION
#num Z3_OP_PR_IFF_TRUE
#num Z3_OP_PR_IFF_FALSE
#num Z3_OP_PR_COMMUTATIVITY
#num Z3_OP_PR_DEF_AXIOM
#num Z3_OP_PR_DEF_INTRO
#num Z3_OP_PR_APPLY_DEF
#num Z3_OP_PR_IFF_OEQ
#num Z3_OP_PR_NNF_POS
#num Z3_OP_PR_NNF_NEG
#num Z3_OP_PR_NNF_STAR
#num Z3_OP_PR_CNF_STAR
#num Z3_OP_PR_SKOLEMIZE
#num Z3_OP_PR_MODUS_PONENS_OEQ
#num Z3_OP_PR_TH_LEMMA
#num Z3_OP_PR_HYPER_RESOLVE
#num Z3_OP_RA_STORE
#num Z3_OP_RA_EMPTY
#num Z3_OP_RA_IS_EMPTY
#num Z3_OP_RA_JOIN
#num Z3_OP_RA_UNION
#num Z3_OP_RA_WIDEN
#num Z3_OP_RA_PROJECT
#num Z3_OP_RA_FILTER
#num Z3_OP_RA_NEGATION_FILTER
#num Z3_OP_RA_RENAME
#num Z3_OP_RA_COMPLEMENT
#num Z3_OP_RA_SELECT
#num Z3_OP_RA_CLONE
#num Z3_OP_FD_CONSTANT
#num Z3_OP_FD_LT
#num Z3_OP_SEQ_UNIT
#num Z3_OP_SEQ_EMPTY
#num Z3_OP_SEQ_CONCAT
#num Z3_OP_SEQ_PREFIX
#num Z3_OP_SEQ_SUFFIX
#num Z3_OP_SEQ_CONTAINS
#num Z3_OP_SEQ_EXTRACT
#num Z3_OP_SEQ_REPLACE
#num Z3_OP_SEQ_AT
#num Z3_OP_SEQ_LENGTH
#num Z3_OP_SEQ_INDEX
#num Z3_OP_SEQ_TO_RE
#num Z3_OP_SEQ_IN_RE
#num Z3_OP_STR_TO_INT
#num Z3_OP_INT_TO_STR
#num Z3_OP_RE_PLUS
#num Z3_OP_RE_STAR
#num Z3_OP_RE_OPTION
#num Z3_OP_RE_CONCAT
#num Z3_OP_RE_UNION
#num Z3_OP_RE_RANGE
#num Z3_OP_RE_LOOP
#num Z3_OP_RE_INTERSECT
#num Z3_OP_RE_EMPTY_SET
#num Z3_OP_RE_FULL_SET
#num Z3_OP_RE_COMPLEMENT
#num Z3_OP_LABEL
#num Z3_OP_LABEL_LIT
#num Z3_OP_DT_CONSTRUCTOR
#num Z3_OP_DT_RECOGNISER
#num Z3_OP_DT_ACCESSOR
#num Z3_OP_DT_UPDATE_FIELD
#num Z3_OP_PB_AT_MOST
#num Z3_OP_PB_AT_LEAST
#num Z3_OP_PB_LE
#num Z3_OP_PB_GE
#num Z3_OP_PB_EQ
#num Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN
#num Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY
#num Z3_OP_FPA_RM_TOWARD_POSITIVE
#num Z3_OP_FPA_RM_TOWARD_NEGATIVE
#num Z3_OP_FPA_RM_TOWARD_ZERO
#num Z3_OP_FPA_NUM
#num Z3_OP_FPA_PLUS_INF
#num Z3_OP_FPA_MINUS_INF
#num Z3_OP_FPA_NAN
#num Z3_OP_FPA_PLUS_ZERO
#num Z3_OP_FPA_MINUS_ZERO
#num Z3_OP_FPA_ADD
#num Z3_OP_FPA_SUB
#num Z3_OP_FPA_NEG
#num Z3_OP_FPA_MUL
#num Z3_OP_FPA_DIV
#num Z3_OP_FPA_REM
#num Z3_OP_FPA_ABS
#num Z3_OP_FPA_MIN
#num Z3_OP_FPA_MAX
#num Z3_OP_FPA_FMA
#num Z3_OP_FPA_SQRT
#num Z3_OP_FPA_ROUND_TO_INTEGRAL
#num Z3_OP_FPA_EQ
#num Z3_OP_FPA_LT
#num Z3_OP_FPA_GT
#num Z3_OP_FPA_LE
#num Z3_OP_FPA_GE
#num Z3_OP_FPA_IS_NAN
#num Z3_OP_FPA_IS_INF
#num Z3_OP_FPA_IS_ZERO
#num Z3_OP_FPA_IS_NORMAL
#num Z3_OP_FPA_IS_SUBNORMAL
#num Z3_OP_FPA_IS_NEGATIVE
#num Z3_OP_FPA_IS_POSITIVE
#num Z3_OP_FPA_FP
#num Z3_OP_FPA_TO_FP
#num Z3_OP_FPA_TO_FP_UNSIGNED
#num Z3_OP_FPA_TO_UBV
#num Z3_OP_FPA_TO_SBV
#num Z3_OP_FPA_TO_REAL
#num Z3_OP_FPA_TO_IEEE_BV
#num Z3_OP_FPA_BVWRAP
#num Z3_OP_FPA_BV2RM
#num Z3_OP_INTERNAL
#num Z3_OP_UNINTERPRETED
{- typedef enum {
            Z3_PK_UINT,
            Z3_PK_BOOL,
            Z3_PK_DOUBLE,
            Z3_PK_SYMBOL,
            Z3_PK_STRING,
            Z3_PK_OTHER,
            Z3_PK_INVALID
        } Z3_param_kind; -}
#integral_t Z3_param_kind
#num Z3_PK_UINT
#num Z3_PK_BOOL
#num Z3_PK_DOUBLE
#num Z3_PK_SYMBOL
#num Z3_PK_STRING
#num Z3_PK_OTHER
#num Z3_PK_INVALID
{- typedef enum {
            Z3_PRINT_SMTLIB_FULL,
            Z3_PRINT_LOW_LEVEL,
            Z3_PRINT_SMTLIB2_COMPLIANT
        } Z3_ast_print_mode; -}
#integral_t Z3_ast_print_mode
#num Z3_PRINT_SMTLIB_FULL
#num Z3_PRINT_LOW_LEVEL
#num Z3_PRINT_SMTLIB2_COMPLIANT
{- typedef enum {
            Z3_OK,
            Z3_SORT_ERROR,
            Z3_IOB,
            Z3_INVALID_ARG,
            Z3_PARSER_ERROR,
            Z3_NO_PARSER,
            Z3_INVALID_PATTERN,
            Z3_MEMOUT_FAIL,
            Z3_FILE_ACCESS_ERROR,
            Z3_INTERNAL_FATAL,
            Z3_INVALID_USAGE,
            Z3_DEC_REF_ERROR,
            Z3_EXCEPTION
        } Z3_error_code; -}
#integral_t Z3_error_code
#num Z3_OK
#num Z3_SORT_ERROR
#num Z3_IOB
#num Z3_INVALID_ARG
#num Z3_PARSER_ERROR
#num Z3_NO_PARSER
#num Z3_INVALID_PATTERN
#num Z3_MEMOUT_FAIL
#num Z3_FILE_ACCESS_ERROR
#num Z3_INTERNAL_FATAL
#num Z3_INVALID_USAGE
#num Z3_DEC_REF_ERROR
#num Z3_EXCEPTION
#ccall Z3_error_handler , <Z3_context> -> <Z3_error_code> -> IO ()
{- typedef enum {
            Z3_GOAL_PRECISE, Z3_GOAL_UNDER, Z3_GOAL_OVER, Z3_GOAL_UNDER_OVER
        } Z3_goal_prec; -}
#integral_t Z3_goal_prec
#num Z3_GOAL_PRECISE
#num Z3_GOAL_UNDER
#num Z3_GOAL_OVER
#num Z3_GOAL_UNDER_OVER
#ccall Z3_global_param_set , <Z3_string> -> <Z3_string> -> IO ()
#ccall Z3_global_param_reset_all , IO ()
#ccall Z3_global_param_get , <Z3_string> -> <Z3_string_ptr> -> IO CInt
#ccall Z3_mk_config , IO <Z3_config>
#ccall Z3_del_config , <Z3_config> -> IO ()
#ccall Z3_set_param_value , <Z3_config> -> <Z3_string> -> <Z3_string> -> IO ()
#ccall Z3_mk_context , <Z3_config> -> IO <Z3_context>
#ccall Z3_mk_context_rc , <Z3_config> -> IO <Z3_context>
#ccall Z3_del_context , <Z3_context> -> IO ()
#ccall Z3_inc_ref , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_dec_ref , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_update_param_value , <Z3_context> -> <Z3_string> -> <Z3_string> -> IO ()
#ccall Z3_interrupt , <Z3_context> -> IO ()
#ccall Z3_mk_params , <Z3_context> -> IO <Z3_params>
#ccall Z3_params_inc_ref , <Z3_context> -> <Z3_params> -> IO ()
#ccall Z3_params_dec_ref , <Z3_context> -> <Z3_params> -> IO ()
#ccall Z3_params_set_bool , <Z3_context> -> <Z3_params> -> <Z3_symbol> -> CInt -> IO ()
#ccall Z3_params_set_uint , <Z3_context> -> <Z3_params> -> <Z3_symbol> -> CUInt -> IO ()
#ccall Z3_params_set_double , <Z3_context> -> <Z3_params> -> <Z3_symbol> -> CDouble -> IO ()
#ccall Z3_params_set_symbol , <Z3_context> -> <Z3_params> -> <Z3_symbol> -> <Z3_symbol> -> IO ()
#ccall Z3_params_to_string , <Z3_context> -> <Z3_params> -> IO <Z3_string>
#ccall Z3_params_validate , <Z3_context> -> <Z3_params> -> <Z3_param_descrs> -> IO ()
#ccall Z3_param_descrs_inc_ref , <Z3_context> -> <Z3_param_descrs> -> IO ()
#ccall Z3_param_descrs_dec_ref , <Z3_context> -> <Z3_param_descrs> -> IO ()
#ccall Z3_param_descrs_get_kind , <Z3_context> -> <Z3_param_descrs> -> <Z3_symbol> -> IO <Z3_param_kind>
#ccall Z3_param_descrs_size , <Z3_context> -> <Z3_param_descrs> -> IO ()
#ccall Z3_param_descrs_get_name , <Z3_context> -> <Z3_param_descrs> -> CUInt -> IO <Z3_symbol>
#ccall Z3_param_descrs_get_documentation , <Z3_context> -> <Z3_param_descrs> -> <Z3_symbol> -> IO <Z3_string>
#ccall Z3_param_descrs_to_string , <Z3_context> -> <Z3_param_descrs> -> IO <Z3_string>
#ccall Z3_mk_int_symbol , <Z3_context> -> CInt -> IO <Z3_symbol>
#ccall Z3_mk_string_symbol , <Z3_context> -> <Z3_string> -> IO <Z3_symbol>
#ccall Z3_mk_uninterpreted_sort , <Z3_context> -> <Z3_symbol> -> IO <Z3_sort>
#ccall Z3_mk_bool_sort , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_int_sort , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_real_sort , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_bv_sort , <Z3_context> -> CUInt -> IO <Z3_sort>
#ccall Z3_mk_finite_domain_sort , <Z3_context> -> <Z3_symbol> -> CULong -> IO <Z3_sort>
#ccall Z3_mk_array_sort , <Z3_context> -> <Z3_sort> -> <Z3_sort> -> IO <Z3_sort>
#ccall Z3_mk_array_sort_n , <Z3_context> -> CUInt -> Ptr <Z3_sort> -> <Z3_sort> -> IO <Z3_sort>
#ccall Z3_mk_tuple_sort , <Z3_context> -> <Z3_symbol> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_sort> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> IO <Z3_sort>
#ccall Z3_mk_enumeration_sort , <Z3_context> -> <Z3_symbol> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> IO <Z3_sort>
#ccall Z3_mk_list_sort , <Z3_context> -> <Z3_symbol> -> <Z3_sort> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> IO <Z3_sort>
#ccall Z3_mk_constructor , <Z3_context> -> <Z3_symbol> -> <Z3_symbol> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_sort> -> Ptr CUInt -> IO <Z3_constructor>
#ccall Z3_del_constructor , <Z3_context> -> <Z3_constructor> -> IO ()
#ccall Z3_mk_datatype , <Z3_context> -> <Z3_symbol> -> CUInt -> Ptr <Z3_constructor> -> IO <Z3_sort>
#ccall Z3_mk_constructor_list , <Z3_context> -> CUInt -> Ptr <Z3_constructor> -> IO <Z3_constructor_list>
#ccall Z3_del_constructor_list , <Z3_context> -> <Z3_constructor_list> -> IO ()
#ccall Z3_mk_datatypes , <Z3_context> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_sort> -> Ptr <Z3_constructor_list> -> IO ()
#ccall Z3_query_constructor , <Z3_context> -> <Z3_constructor> -> CUInt -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> Ptr <Z3_func_decl> -> IO ()
#ccall Z3_mk_func_decl , <Z3_context> -> <Z3_symbol> -> CUInt -> Ptr <Z3_sort> -> <Z3_sort> -> IO <Z3_func_decl>
#ccall Z3_mk_app , <Z3_context> -> <Z3_func_decl> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_const , <Z3_context> -> <Z3_symbol> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fresh_func_decl , <Z3_context> -> <Z3_string> -> CUInt -> Ptr <Z3_sort> -> <Z3_sort> -> IO <Z3_func_decl>
#ccall Z3_mk_fresh_const , <Z3_context> -> <Z3_string> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_true , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_false , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_eq , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_distinct , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_not , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_ite , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_iff , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_implies , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_xor , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_and , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_or , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_add , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_mul , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_sub , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_unary_minus , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_div , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_mod , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_rem , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_power , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_lt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_le , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_gt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_ge , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_int2real , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_real2int , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_is_int , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvnot , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvredand , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvredor , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvand , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvor , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvxor , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvnand , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvnor , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvxnor , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvneg , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvadd , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsub , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvmul , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvudiv , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsdiv , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvurem , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsrem , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsmod , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvult , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvslt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvule , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsle , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvuge , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsge , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvugt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsgt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_concat , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_extract , <Z3_context> -> CUInt -> CUInt -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_sign_ext , <Z3_context> -> CUInt -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_zero_ext , <Z3_context> -> CUInt -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_repeat , <Z3_context> -> CUInt -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvshl , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvlshr , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvashr , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_rotate_left , <Z3_context> -> CUInt -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_rotate_right , <Z3_context> -> CUInt -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_ext_rotate_left , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_ext_rotate_right , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_int2bv , <Z3_context> -> CUInt -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bv2int , <Z3_context> -> <Z3_ast> -> CInt -> IO <Z3_ast>
#ccall Z3_mk_bvadd_no_overflow , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> CInt -> IO <Z3_ast>
#ccall Z3_mk_bvadd_no_underflow , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsub_no_overflow , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvsub_no_underflow , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> CInt -> IO <Z3_ast>
#ccall Z3_mk_bvsdiv_no_overflow , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvneg_no_overflow , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_bvmul_no_overflow , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> CInt -> IO <Z3_ast>
#ccall Z3_mk_bvmul_no_underflow , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_select , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_select_n , <Z3_context> -> <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_store , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_store_n , <Z3_context> -> <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_const_array , <Z3_context> -> <Z3_sort> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_map , <Z3_context> -> <Z3_func_decl> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_array_default , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_as_array , <Z3_context> -> <Z3_func_decl> -> IO <Z3_ast>
#ccall Z3_mk_set_sort , <Z3_context> -> <Z3_sort> -> IO <Z3_sort>
#ccall Z3_mk_empty_set , <Z3_context> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_full_set , <Z3_context> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_set_add , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_set_del , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_set_union , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_set_intersect , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_set_difference , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_set_complement , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_set_member , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_set_subset , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_array_ext , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_numeral , <Z3_context> -> <Z3_string> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_real , <Z3_context> -> CInt -> CInt -> IO <Z3_ast>
#ccall Z3_mk_int , <Z3_context> -> CInt -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_unsigned_int , <Z3_context> -> CUInt -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_int64 , <Z3_context> -> CLong -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_unsigned_int64 , <Z3_context> -> CULong -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_bv_numeral , <Z3_context> -> CUInt -> Ptr CInt -> IO <Z3_ast>
#ccall Z3_mk_seq_sort , <Z3_context> -> <Z3_sort> -> IO <Z3_sort>
#ccall Z3_is_seq_sort , <Z3_context> -> <Z3_sort> -> IO CInt
#ccall Z3_mk_re_sort , <Z3_context> -> <Z3_sort> -> IO <Z3_sort>
#ccall Z3_is_re_sort , <Z3_context> -> <Z3_sort> -> IO CInt
#ccall Z3_mk_string_sort , <Z3_context> -> IO <Z3_sort>
#ccall Z3_is_string_sort , <Z3_context> -> <Z3_sort> -> IO CInt
#ccall Z3_mk_string , <Z3_context> -> <Z3_string> -> IO <Z3_ast>
#ccall Z3_is_string , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_get_string , <Z3_context> -> <Z3_ast> -> IO <Z3_string>
#ccall Z3_mk_seq_empty , <Z3_context> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_seq_unit , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_concat , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_prefix , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_suffix , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_contains , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_extract , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_replace , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_at , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_length , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_index , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_str_to_int , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_int_to_str , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_to_re , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_seq_in_re , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_plus , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_star , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_option , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_union , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_concat , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_range , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_loop , <Z3_context> -> <Z3_ast> -> CUInt -> CUInt -> IO <Z3_ast>
#ccall Z3_mk_re_intersect , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_complement , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_re_empty , <Z3_context> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_re_full , <Z3_context> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_pattern , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_pattern>
#ccall Z3_mk_bound , <Z3_context> -> CUInt -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_forall , <Z3_context> -> CUInt -> CUInt -> Ptr <Z3_pattern> -> CUInt -> Ptr <Z3_sort> -> Ptr <Z3_symbol> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_exists , <Z3_context> -> CUInt -> CUInt -> Ptr <Z3_pattern> -> CUInt -> Ptr <Z3_sort> -> Ptr <Z3_symbol> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_quantifier , <Z3_context> -> CInt -> CUInt -> CUInt -> Ptr <Z3_pattern> -> CUInt -> Ptr <Z3_sort> -> Ptr <Z3_symbol> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_quantifier_ex , <Z3_context> -> CInt -> CUInt -> <Z3_symbol> -> <Z3_symbol> -> CUInt -> Ptr <Z3_pattern> -> CUInt -> Ptr <Z3_ast> -> CUInt -> Ptr <Z3_sort> -> Ptr <Z3_symbol> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_forall_const , <Z3_context> -> CUInt -> CUInt -> Ptr <Z3_app> -> CUInt -> Ptr <Z3_pattern> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_exists_const , <Z3_context> -> CUInt -> CUInt -> Ptr <Z3_app> -> CUInt -> Ptr <Z3_pattern> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_quantifier_const , <Z3_context> -> CInt -> CUInt -> CUInt -> Ptr <Z3_app> -> CUInt -> Ptr <Z3_pattern> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_quantifier_const_ex , <Z3_context> -> CInt -> CUInt -> <Z3_symbol> -> <Z3_symbol> -> CUInt -> Ptr <Z3_app> -> CUInt -> Ptr <Z3_pattern> -> CUInt -> Ptr <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_get_symbol_kind , <Z3_context> -> <Z3_symbol> -> IO <Z3_symbol_kind>
#ccall Z3_get_symbol_int , <Z3_context> -> <Z3_symbol> -> IO CInt
#ccall Z3_get_symbol_string , <Z3_context> -> <Z3_symbol> -> IO <Z3_string>
#ccall Z3_get_sort_name , <Z3_context> -> <Z3_sort> -> IO <Z3_symbol>
#ccall Z3_get_sort_id , <Z3_context> -> <Z3_sort> -> IO ()
#ccall Z3_sort_to_ast , <Z3_context> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_is_eq_sort , <Z3_context> -> <Z3_sort> -> <Z3_sort> -> IO CInt
#ccall Z3_get_sort_kind , <Z3_context> -> <Z3_sort> -> IO <Z3_sort_kind>
#ccall Z3_get_bv_sort_size , <Z3_context> -> <Z3_sort> -> IO ()
#ccall Z3_get_finite_domain_sort_size , <Z3_context> -> <Z3_sort> -> Ptr CULong -> IO CInt
#ccall Z3_get_array_sort_domain , <Z3_context> -> <Z3_sort> -> IO <Z3_sort>
#ccall Z3_get_array_sort_range , <Z3_context> -> <Z3_sort> -> IO <Z3_sort>
#ccall Z3_get_tuple_sort_mk_decl , <Z3_context> -> <Z3_sort> -> IO <Z3_func_decl>
#ccall Z3_get_tuple_sort_num_fields , <Z3_context> -> <Z3_sort> -> IO ()
#ccall Z3_get_tuple_sort_field_decl , <Z3_context> -> <Z3_sort> -> CUInt -> IO <Z3_func_decl>
#ccall Z3_get_datatype_sort_num_constructors , <Z3_context> -> <Z3_sort> -> IO ()
#ccall Z3_get_datatype_sort_constructor , <Z3_context> -> <Z3_sort> -> CUInt -> IO <Z3_func_decl>
#ccall Z3_get_datatype_sort_recognizer , <Z3_context> -> <Z3_sort> -> CUInt -> IO <Z3_func_decl>
#ccall Z3_get_datatype_sort_constructor_accessor , <Z3_context> -> <Z3_sort> -> CUInt -> CUInt -> IO <Z3_func_decl>
#ccall Z3_datatype_update_field , <Z3_context> -> <Z3_func_decl> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_get_relation_arity , <Z3_context> -> <Z3_sort> -> IO ()
#ccall Z3_get_relation_column , <Z3_context> -> <Z3_sort> -> CUInt -> IO <Z3_sort>
#ccall Z3_mk_atmost , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_mk_atleast , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_mk_pble , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> Ptr CInt -> CInt -> IO <Z3_ast>
#ccall Z3_mk_pbge , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> Ptr CInt -> CInt -> IO <Z3_ast>
#ccall Z3_mk_pbeq , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> Ptr CInt -> CInt -> IO <Z3_ast>
#ccall Z3_func_decl_to_ast , <Z3_context> -> <Z3_func_decl> -> IO <Z3_ast>
#ccall Z3_is_eq_func_decl , <Z3_context> -> <Z3_func_decl> -> <Z3_func_decl> -> IO CInt
#ccall Z3_get_func_decl_id , <Z3_context> -> <Z3_func_decl> -> IO ()
#ccall Z3_get_decl_name , <Z3_context> -> <Z3_func_decl> -> IO <Z3_symbol>
#ccall Z3_get_decl_kind , <Z3_context> -> <Z3_func_decl> -> IO <Z3_decl_kind>
#ccall Z3_get_domain_size , <Z3_context> -> <Z3_func_decl> -> IO ()
#ccall Z3_get_arity , <Z3_context> -> <Z3_func_decl> -> IO ()
#ccall Z3_get_domain , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO <Z3_sort>
#ccall Z3_get_range , <Z3_context> -> <Z3_func_decl> -> IO <Z3_sort>
#ccall Z3_get_decl_num_parameters , <Z3_context> -> <Z3_func_decl> -> IO ()
#ccall Z3_get_decl_parameter_kind , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO <Z3_parameter_kind>
#ccall Z3_get_decl_int_parameter , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO CInt
#ccall Z3_get_decl_double_parameter , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO CDouble
#ccall Z3_get_decl_symbol_parameter , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO <Z3_symbol>
#ccall Z3_get_decl_sort_parameter , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO <Z3_sort>
#ccall Z3_get_decl_ast_parameter , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO <Z3_ast>
#ccall Z3_get_decl_func_decl_parameter , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO <Z3_func_decl>
#ccall Z3_get_decl_rational_parameter , <Z3_context> -> <Z3_func_decl> -> CUInt -> IO <Z3_string>
#ccall Z3_app_to_ast , <Z3_context> -> <Z3_app> -> IO <Z3_ast>
#ccall Z3_get_app_decl , <Z3_context> -> <Z3_app> -> IO <Z3_func_decl>
#ccall Z3_get_app_num_args , <Z3_context> -> <Z3_app> -> IO ()
#ccall Z3_get_app_arg , <Z3_context> -> <Z3_app> -> CUInt -> IO <Z3_ast>
#ccall Z3_is_eq_ast , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO CInt
#ccall Z3_get_ast_id , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_get_ast_hash , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_get_sort , <Z3_context> -> <Z3_ast> -> IO <Z3_sort>
#ccall Z3_is_well_sorted , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_get_bool_value , <Z3_context> -> <Z3_ast> -> IO <Z3_lbool>
#ccall Z3_get_ast_kind , <Z3_context> -> <Z3_ast> -> IO <Z3_ast_kind>
#ccall Z3_is_app , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_is_numeral_ast , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_is_algebraic_number , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_to_app , <Z3_context> -> <Z3_ast> -> IO <Z3_app>
#ccall Z3_to_func_decl , <Z3_context> -> <Z3_ast> -> IO <Z3_func_decl>
#ccall Z3_get_numeral_string , <Z3_context> -> <Z3_ast> -> IO <Z3_string>
#ccall Z3_get_numeral_decimal_string , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_string>
#ccall Z3_get_numerator , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_get_denominator , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_get_numeral_small , <Z3_context> -> <Z3_ast> -> Ptr CLong -> Ptr CLong -> IO CInt
#ccall Z3_get_numeral_int , <Z3_context> -> <Z3_ast> -> Ptr CInt -> IO CInt
#ccall Z3_get_numeral_uint , <Z3_context> -> <Z3_ast> -> Ptr CUInt -> IO CInt
#ccall Z3_get_numeral_uint64 , <Z3_context> -> <Z3_ast> -> Ptr CULong -> IO CInt
#ccall Z3_get_numeral_int64 , <Z3_context> -> <Z3_ast> -> Ptr CLong -> IO CInt
#ccall Z3_get_numeral_rational_int64 , <Z3_context> -> <Z3_ast> -> Ptr CLong -> Ptr CLong -> IO CInt
#ccall Z3_get_algebraic_number_lower , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_get_algebraic_number_upper , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_pattern_to_ast , <Z3_context> -> <Z3_pattern> -> IO <Z3_ast>
#ccall Z3_get_pattern_num_terms , <Z3_context> -> <Z3_pattern> -> IO ()
#ccall Z3_get_pattern , <Z3_context> -> <Z3_pattern> -> CUInt -> IO <Z3_ast>
#ccall Z3_get_index_value , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_is_quantifier_forall , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_get_quantifier_weight , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_get_quantifier_num_patterns , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_get_quantifier_pattern_ast , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_pattern>
#ccall Z3_get_quantifier_num_no_patterns , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_get_quantifier_no_pattern_ast , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_get_quantifier_num_bound , <Z3_context> -> <Z3_ast> -> IO ()
#ccall Z3_get_quantifier_bound_name , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_symbol>
#ccall Z3_get_quantifier_bound_sort , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_sort>
#ccall Z3_get_quantifier_body , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_simplify , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_simplify_ex , <Z3_context> -> <Z3_ast> -> <Z3_params> -> IO <Z3_ast>
#ccall Z3_simplify_get_help , <Z3_context> -> IO <Z3_string>
#ccall Z3_simplify_get_param_descrs , <Z3_context> -> IO <Z3_param_descrs>
#ccall Z3_update_term , <Z3_context> -> <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_substitute , <Z3_context> -> <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_substitute_vars , <Z3_context> -> <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast>
#ccall Z3_translate , <Z3_context> -> <Z3_ast> -> <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_model , <Z3_context> -> IO <Z3_model>
#ccall Z3_model_inc_ref , <Z3_context> -> <Z3_model> -> IO ()
#ccall Z3_model_dec_ref , <Z3_context> -> <Z3_model> -> IO ()
#ccall Z3_model_eval , <Z3_context> -> <Z3_model> -> <Z3_ast> -> CInt -> Ptr <Z3_ast> -> IO CInt
#ccall Z3_model_get_const_interp , <Z3_context> -> <Z3_model> -> <Z3_func_decl> -> IO <Z3_ast>
#ccall Z3_model_has_interp , <Z3_context> -> <Z3_model> -> <Z3_func_decl> -> IO CInt
#ccall Z3_model_get_func_interp , <Z3_context> -> <Z3_model> -> <Z3_func_decl> -> IO <Z3_func_interp>
#ccall Z3_model_get_num_consts , <Z3_context> -> <Z3_model> -> IO ()
#ccall Z3_model_get_const_decl , <Z3_context> -> <Z3_model> -> CUInt -> IO <Z3_func_decl>
#ccall Z3_model_get_num_funcs , <Z3_context> -> <Z3_model> -> IO ()
#ccall Z3_model_get_func_decl , <Z3_context> -> <Z3_model> -> CUInt -> IO <Z3_func_decl>
#ccall Z3_model_get_num_sorts , <Z3_context> -> <Z3_model> -> IO ()
#ccall Z3_model_get_sort , <Z3_context> -> <Z3_model> -> CUInt -> IO <Z3_sort>
#ccall Z3_model_get_sort_universe , <Z3_context> -> <Z3_model> -> <Z3_sort> -> IO <Z3_ast_vector>
#ccall Z3_is_as_array , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_get_as_array_func_decl , <Z3_context> -> <Z3_ast> -> IO <Z3_func_decl>
#ccall Z3_add_func_interp , <Z3_context> -> <Z3_model> -> <Z3_func_decl> -> <Z3_ast> -> IO <Z3_func_interp>
#ccall Z3_add_const_interp , <Z3_context> -> <Z3_model> -> <Z3_func_decl> -> <Z3_ast> -> IO ()
#ccall Z3_func_interp_inc_ref , <Z3_context> -> <Z3_func_interp> -> IO ()
#ccall Z3_func_interp_dec_ref , <Z3_context> -> <Z3_func_interp> -> IO ()
#ccall Z3_func_interp_get_num_entries , <Z3_context> -> <Z3_func_interp> -> IO ()
#ccall Z3_func_interp_get_entry , <Z3_context> -> <Z3_func_interp> -> CUInt -> IO <Z3_func_entry>
#ccall Z3_func_interp_get_else , <Z3_context> -> <Z3_func_interp> -> IO <Z3_ast>
#ccall Z3_func_interp_set_else , <Z3_context> -> <Z3_func_interp> -> <Z3_ast> -> IO ()
#ccall Z3_func_interp_get_arity , <Z3_context> -> <Z3_func_interp> -> IO ()
#ccall Z3_func_interp_add_entry , <Z3_context> -> <Z3_func_interp> -> <Z3_ast_vector> -> <Z3_ast> -> IO ()
#ccall Z3_func_entry_inc_ref , <Z3_context> -> <Z3_func_entry> -> IO ()
#ccall Z3_func_entry_dec_ref , <Z3_context> -> <Z3_func_entry> -> IO ()
#ccall Z3_func_entry_get_value , <Z3_context> -> <Z3_func_entry> -> IO <Z3_ast>
#ccall Z3_func_entry_get_num_args , <Z3_context> -> <Z3_func_entry> -> IO ()
#ccall Z3_func_entry_get_arg , <Z3_context> -> <Z3_func_entry> -> CUInt -> IO <Z3_ast>
#ccall Z3_open_log , <Z3_string> -> IO CInt
#ccall Z3_append_log , <Z3_string> -> IO ()
#ccall Z3_close_log , IO ()
#ccall Z3_toggle_warning_messages , CInt -> IO ()
#ccall Z3_set_ast_print_mode , <Z3_context> -> <Z3_ast_print_mode> -> IO ()
#ccall Z3_ast_to_string , <Z3_context> -> <Z3_ast> -> IO <Z3_string>
#ccall Z3_pattern_to_string , <Z3_context> -> <Z3_pattern> -> IO <Z3_string>
#ccall Z3_sort_to_string , <Z3_context> -> <Z3_sort> -> IO <Z3_string>
#ccall Z3_func_decl_to_string , <Z3_context> -> <Z3_func_decl> -> IO <Z3_string>
#ccall Z3_model_to_string , <Z3_context> -> <Z3_model> -> IO <Z3_string>
#ccall Z3_benchmark_to_smtlib_string , <Z3_context> -> <Z3_string> -> <Z3_string> -> <Z3_string> -> <Z3_string> -> CUInt -> Ptr <Z3_ast> -> <Z3_ast> -> IO <Z3_string>
#ccall Z3_parse_smtlib2_string , <Z3_context> -> <Z3_string> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_sort> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_func_decl> -> IO <Z3_ast>
#ccall Z3_parse_smtlib2_file , <Z3_context> -> <Z3_string> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_sort> -> CUInt -> Ptr <Z3_symbol> -> Ptr <Z3_func_decl> -> IO <Z3_ast>
#ccall Z3_get_parser_error , <Z3_context> -> IO <Z3_string>
#ccall Z3_get_error_code , <Z3_context> -> IO <Z3_error_code>
#ccall Z3_set_error_handler , <Z3_context> -> <Z3_error_handler> -> IO ()
#ccall Z3_set_error , <Z3_context> -> <Z3_error_code> -> IO ()
#ccall Z3_get_error_msg , <Z3_context> -> <Z3_error_code> -> IO <Z3_string>
#ccall Z3_get_error_msg_ex , <Z3_context> -> <Z3_error_code> -> IO <Z3_string>
#ccall Z3_get_version , Ptr CUInt -> Ptr CUInt -> Ptr CUInt -> Ptr CUInt -> IO ()
#ccall Z3_get_full_version , IO <Z3_string>
#ccall Z3_enable_trace , <Z3_string> -> IO ()
#ccall Z3_disable_trace , <Z3_string> -> IO ()
#ccall Z3_reset_memory , IO ()
#ccall Z3_finalize_memory , IO ()
#ccall Z3_mk_goal , <Z3_context> -> CInt -> CInt -> CInt -> IO <Z3_goal>
#ccall Z3_goal_inc_ref , <Z3_context> -> <Z3_goal> -> IO ()
#ccall Z3_goal_dec_ref , <Z3_context> -> <Z3_goal> -> IO ()
#ccall Z3_goal_precision , <Z3_context> -> <Z3_goal> -> IO <Z3_goal_prec>
#ccall Z3_goal_assert , <Z3_context> -> <Z3_goal> -> <Z3_ast> -> IO ()
#ccall Z3_goal_inconsistent , <Z3_context> -> <Z3_goal> -> IO CInt
#ccall Z3_goal_depth , <Z3_context> -> <Z3_goal> -> IO ()
#ccall Z3_goal_reset , <Z3_context> -> <Z3_goal> -> IO ()
#ccall Z3_goal_size , <Z3_context> -> <Z3_goal> -> IO ()
#ccall Z3_goal_formula , <Z3_context> -> <Z3_goal> -> CUInt -> IO <Z3_ast>
#ccall Z3_goal_num_exprs , <Z3_context> -> <Z3_goal> -> IO ()
#ccall Z3_goal_is_decided_sat , <Z3_context> -> <Z3_goal> -> IO CInt
#ccall Z3_goal_is_decided_unsat , <Z3_context> -> <Z3_goal> -> IO CInt
#ccall Z3_goal_translate , <Z3_context> -> <Z3_goal> -> <Z3_context> -> IO <Z3_goal>
#ccall Z3_goal_to_string , <Z3_context> -> <Z3_goal> -> IO <Z3_string>
#ccall Z3_mk_tactic , <Z3_context> -> <Z3_string> -> IO <Z3_tactic>
#ccall Z3_tactic_inc_ref , <Z3_context> -> <Z3_tactic> -> IO ()
#ccall Z3_tactic_dec_ref , <Z3_context> -> <Z3_tactic> -> IO ()
#ccall Z3_mk_probe , <Z3_context> -> <Z3_string> -> IO <Z3_probe>
#ccall Z3_probe_inc_ref , <Z3_context> -> <Z3_probe> -> IO ()
#ccall Z3_probe_dec_ref , <Z3_context> -> <Z3_probe> -> IO ()
#ccall Z3_tactic_and_then , <Z3_context> -> <Z3_tactic> -> <Z3_tactic> -> IO <Z3_tactic>
#ccall Z3_tactic_or_else , <Z3_context> -> <Z3_tactic> -> <Z3_tactic> -> IO <Z3_tactic>
#ccall Z3_tactic_par_or , <Z3_context> -> CUInt -> Ptr <Z3_tactic> -> IO <Z3_tactic>
#ccall Z3_tactic_par_and_then , <Z3_context> -> <Z3_tactic> -> <Z3_tactic> -> IO <Z3_tactic>
#ccall Z3_tactic_try_for , <Z3_context> -> <Z3_tactic> -> CUInt -> IO <Z3_tactic>
#ccall Z3_tactic_when , <Z3_context> -> <Z3_probe> -> <Z3_tactic> -> IO <Z3_tactic>
#ccall Z3_tactic_cond , <Z3_context> -> <Z3_probe> -> <Z3_tactic> -> <Z3_tactic> -> IO <Z3_tactic>
#ccall Z3_tactic_repeat , <Z3_context> -> <Z3_tactic> -> CUInt -> IO <Z3_tactic>
#ccall Z3_tactic_skip , <Z3_context> -> IO <Z3_tactic>
#ccall Z3_tactic_fail , <Z3_context> -> IO <Z3_tactic>
#ccall Z3_tactic_fail_if , <Z3_context> -> <Z3_probe> -> IO <Z3_tactic>
#ccall Z3_tactic_fail_if_not_decided , <Z3_context> -> IO <Z3_tactic>
#ccall Z3_tactic_using_params , <Z3_context> -> <Z3_tactic> -> <Z3_params> -> IO <Z3_tactic>
#ccall Z3_probe_const , <Z3_context> -> CDouble -> IO <Z3_probe>
#ccall Z3_probe_lt , <Z3_context> -> <Z3_probe> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_probe_gt , <Z3_context> -> <Z3_probe> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_probe_le , <Z3_context> -> <Z3_probe> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_probe_ge , <Z3_context> -> <Z3_probe> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_probe_eq , <Z3_context> -> <Z3_probe> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_probe_and , <Z3_context> -> <Z3_probe> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_probe_or , <Z3_context> -> <Z3_probe> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_probe_not , <Z3_context> -> <Z3_probe> -> IO <Z3_probe>
#ccall Z3_get_num_tactics , <Z3_context> -> IO ()
#ccall Z3_get_tactic_name , <Z3_context> -> CUInt -> IO <Z3_string>
#ccall Z3_get_num_probes , <Z3_context> -> IO ()
#ccall Z3_get_probe_name , <Z3_context> -> CUInt -> IO <Z3_string>
#ccall Z3_tactic_get_help , <Z3_context> -> <Z3_tactic> -> IO <Z3_string>
#ccall Z3_tactic_get_param_descrs , <Z3_context> -> <Z3_tactic> -> IO <Z3_param_descrs>
#ccall Z3_tactic_get_descr , <Z3_context> -> <Z3_string> -> IO <Z3_string>
#ccall Z3_probe_get_descr , <Z3_context> -> <Z3_string> -> IO <Z3_string>
#ccall Z3_probe_apply , <Z3_context> -> <Z3_probe> -> <Z3_goal> -> IO CDouble
#ccall Z3_tactic_apply , <Z3_context> -> <Z3_tactic> -> <Z3_goal> -> IO <Z3_apply_result>
#ccall Z3_tactic_apply_ex , <Z3_context> -> <Z3_tactic> -> <Z3_goal> -> <Z3_params> -> IO <Z3_apply_result>
#ccall Z3_apply_result_inc_ref , <Z3_context> -> <Z3_apply_result> -> IO ()
#ccall Z3_apply_result_dec_ref , <Z3_context> -> <Z3_apply_result> -> IO ()
#ccall Z3_apply_result_to_string , <Z3_context> -> <Z3_apply_result> -> IO <Z3_string>
#ccall Z3_apply_result_get_num_subgoals , <Z3_context> -> <Z3_apply_result> -> IO ()
#ccall Z3_apply_result_get_subgoal , <Z3_context> -> <Z3_apply_result> -> CUInt -> IO <Z3_goal>
#ccall Z3_apply_result_convert_model , <Z3_context> -> <Z3_apply_result> -> CUInt -> <Z3_model> -> IO <Z3_model>
#ccall Z3_mk_solver , <Z3_context> -> IO <Z3_solver>
#ccall Z3_mk_simple_solver , <Z3_context> -> IO <Z3_solver>
#ccall Z3_mk_solver_for_logic , <Z3_context> -> <Z3_symbol> -> IO <Z3_solver>
#ccall Z3_mk_solver_from_tactic , <Z3_context> -> <Z3_tactic> -> IO <Z3_solver>
#ccall Z3_solver_translate , <Z3_context> -> <Z3_solver> -> <Z3_context> -> IO <Z3_solver>
#ccall Z3_solver_get_help , <Z3_context> -> <Z3_solver> -> IO <Z3_string>
#ccall Z3_solver_get_param_descrs , <Z3_context> -> <Z3_solver> -> IO <Z3_param_descrs>
#ccall Z3_solver_set_params , <Z3_context> -> <Z3_solver> -> <Z3_params> -> IO ()
#ccall Z3_solver_inc_ref , <Z3_context> -> <Z3_solver> -> IO ()
#ccall Z3_solver_dec_ref , <Z3_context> -> <Z3_solver> -> IO ()
#ccall Z3_solver_push , <Z3_context> -> <Z3_solver> -> IO ()
#ccall Z3_solver_pop , <Z3_context> -> <Z3_solver> -> CUInt -> IO ()
#ccall Z3_solver_reset , <Z3_context> -> <Z3_solver> -> IO ()
#ccall Z3_solver_get_num_scopes , <Z3_context> -> <Z3_solver> -> IO ()
#ccall Z3_solver_assert , <Z3_context> -> <Z3_solver> -> <Z3_ast> -> IO ()
#ccall Z3_solver_assert_and_track , <Z3_context> -> <Z3_solver> -> <Z3_ast> -> <Z3_ast> -> IO ()
#ccall Z3_solver_get_assertions , <Z3_context> -> <Z3_solver> -> IO <Z3_ast_vector>
#ccall Z3_solver_from_file , <Z3_context> -> <Z3_solver> -> <Z3_string> -> IO ()
#ccall Z3_solver_from_string , <Z3_context> -> <Z3_solver> -> <Z3_string> -> IO ()
#ccall Z3_solver_check , <Z3_context> -> <Z3_solver> -> IO <Z3_lbool>
#ccall Z3_solver_check_assumptions , <Z3_context> -> <Z3_solver> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_lbool>
#ccall Z3_get_implied_equalities , <Z3_context> -> <Z3_solver> -> CUInt -> Ptr <Z3_ast> -> Ptr CUInt -> IO <Z3_lbool>
#ccall Z3_solver_get_consequences , <Z3_context> -> <Z3_solver> -> <Z3_ast_vector> -> <Z3_ast_vector> -> <Z3_ast_vector> -> IO <Z3_lbool>
#ccall Z3_solver_get_model , <Z3_context> -> <Z3_solver> -> IO <Z3_model>
#ccall Z3_solver_get_proof , <Z3_context> -> <Z3_solver> -> IO <Z3_ast>
#ccall Z3_solver_get_unsat_core , <Z3_context> -> <Z3_solver> -> IO <Z3_ast_vector>
#ccall Z3_solver_get_reason_unknown , <Z3_context> -> <Z3_solver> -> IO <Z3_string>
#ccall Z3_solver_get_statistics , <Z3_context> -> <Z3_solver> -> IO <Z3_stats>
#ccall Z3_solver_to_string , <Z3_context> -> <Z3_solver> -> IO <Z3_string>
#ccall Z3_stats_to_string , <Z3_context> -> <Z3_stats> -> IO <Z3_string>
#ccall Z3_stats_inc_ref , <Z3_context> -> <Z3_stats> -> IO ()
#ccall Z3_stats_dec_ref , <Z3_context> -> <Z3_stats> -> IO ()
#ccall Z3_stats_size , <Z3_context> -> <Z3_stats> -> IO ()
#ccall Z3_stats_get_key , <Z3_context> -> <Z3_stats> -> CUInt -> IO <Z3_string>
#ccall Z3_stats_is_uint , <Z3_context> -> <Z3_stats> -> CUInt -> IO CInt
#ccall Z3_stats_is_double , <Z3_context> -> <Z3_stats> -> CUInt -> IO CInt
#ccall Z3_stats_get_uint_value , <Z3_context> -> <Z3_stats> -> CUInt -> IO ()
#ccall Z3_stats_get_double_value , <Z3_context> -> <Z3_stats> -> CUInt -> IO CDouble
#ccall Z3_get_estimated_alloc_size , IO CULong
#ccall Z3_mk_ast_vector , <Z3_context> -> IO <Z3_ast_vector>
#ccall Z3_ast_vector_inc_ref , <Z3_context> -> <Z3_ast_vector> -> IO ()
#ccall Z3_ast_vector_dec_ref , <Z3_context> -> <Z3_ast_vector> -> IO ()
#ccall Z3_ast_vector_size , <Z3_context> -> <Z3_ast_vector> -> IO ()
#ccall Z3_ast_vector_get , <Z3_context> -> <Z3_ast_vector> -> CUInt -> IO <Z3_ast>
#ccall Z3_ast_vector_set , <Z3_context> -> <Z3_ast_vector> -> CUInt -> <Z3_ast> -> IO ()
#ccall Z3_ast_vector_resize , <Z3_context> -> <Z3_ast_vector> -> CUInt -> IO ()
#ccall Z3_ast_vector_push , <Z3_context> -> <Z3_ast_vector> -> <Z3_ast> -> IO ()
#ccall Z3_ast_vector_translate , <Z3_context> -> <Z3_ast_vector> -> <Z3_context> -> IO <Z3_ast_vector>
#ccall Z3_ast_vector_to_string , <Z3_context> -> <Z3_ast_vector> -> IO <Z3_string>
#ccall Z3_mk_ast_map , <Z3_context> -> IO <Z3_ast_map>
#ccall Z3_ast_map_inc_ref , <Z3_context> -> <Z3_ast_map> -> IO ()
#ccall Z3_ast_map_dec_ref , <Z3_context> -> <Z3_ast_map> -> IO ()
#ccall Z3_ast_map_contains , <Z3_context> -> <Z3_ast_map> -> <Z3_ast> -> IO CInt
#ccall Z3_ast_map_find , <Z3_context> -> <Z3_ast_map> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_ast_map_insert , <Z3_context> -> <Z3_ast_map> -> <Z3_ast> -> <Z3_ast> -> IO ()
#ccall Z3_ast_map_erase , <Z3_context> -> <Z3_ast_map> -> <Z3_ast> -> IO ()
#ccall Z3_ast_map_reset , <Z3_context> -> <Z3_ast_map> -> IO ()
#ccall Z3_ast_map_size , <Z3_context> -> <Z3_ast_map> -> IO ()
#ccall Z3_ast_map_keys , <Z3_context> -> <Z3_ast_map> -> IO <Z3_ast_vector>
#ccall Z3_ast_map_to_string , <Z3_context> -> <Z3_ast_map> -> IO <Z3_string>
#ccall Z3_algebraic_is_value , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_is_pos , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_is_neg , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_is_zero , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_sign , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_add , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_algebraic_sub , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_algebraic_mul , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_algebraic_div , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_algebraic_root , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_algebraic_power , <Z3_context> -> <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_algebraic_lt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_gt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_le , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_ge , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_eq , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_neq , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO CInt
#ccall Z3_algebraic_roots , <Z3_context> -> <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_ast_vector>
#ccall Z3_algebraic_eval , <Z3_context> -> <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> IO CInt
#ccall Z3_polynomial_subresultants , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast_vector>
#ccall Z3_rcf_del , <Z3_context> -> <Z3_rcf_num> -> IO ()
#ccall Z3_rcf_mk_rational , <Z3_context> -> <Z3_string> -> IO <Z3_rcf_num>
#ccall Z3_rcf_mk_small_int , <Z3_context> -> CInt -> IO <Z3_rcf_num>
#ccall Z3_rcf_mk_pi , <Z3_context> -> IO <Z3_rcf_num>
#ccall Z3_rcf_mk_e , <Z3_context> -> IO <Z3_rcf_num>
#ccall Z3_rcf_mk_infinitesimal , <Z3_context> -> IO <Z3_rcf_num>
#ccall Z3_rcf_mk_roots , <Z3_context> -> CUInt -> Ptr <Z3_rcf_num> -> Ptr <Z3_rcf_num> -> IO ()
#ccall Z3_rcf_add , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO <Z3_rcf_num>
#ccall Z3_rcf_sub , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO <Z3_rcf_num>
#ccall Z3_rcf_mul , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO <Z3_rcf_num>
#ccall Z3_rcf_div , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO <Z3_rcf_num>
#ccall Z3_rcf_neg , <Z3_context> -> <Z3_rcf_num> -> IO <Z3_rcf_num>
#ccall Z3_rcf_inv , <Z3_context> -> <Z3_rcf_num> -> IO <Z3_rcf_num>
#ccall Z3_rcf_power , <Z3_context> -> <Z3_rcf_num> -> CUInt -> IO <Z3_rcf_num>
#ccall Z3_rcf_lt , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO CInt
#ccall Z3_rcf_gt , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO CInt
#ccall Z3_rcf_le , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO CInt
#ccall Z3_rcf_ge , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO CInt
#ccall Z3_rcf_eq , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO CInt
#ccall Z3_rcf_neq , <Z3_context> -> <Z3_rcf_num> -> <Z3_rcf_num> -> IO CInt
#ccall Z3_rcf_num_to_string , <Z3_context> -> <Z3_rcf_num> -> CInt -> CInt -> IO <Z3_string>
#ccall Z3_rcf_num_to_decimal_string , <Z3_context> -> <Z3_rcf_num> -> CUInt -> IO <Z3_string>
#ccall Z3_rcf_get_numerator_denominator , <Z3_context> -> <Z3_rcf_num> -> Ptr <Z3_rcf_num> -> Ptr <Z3_rcf_num> -> IO ()
#ccall Z3_mk_fixedpoint , <Z3_context> -> IO <Z3_fixedpoint>
#ccall Z3_fixedpoint_inc_ref , <Z3_context> -> <Z3_fixedpoint> -> IO ()
#ccall Z3_fixedpoint_dec_ref , <Z3_context> -> <Z3_fixedpoint> -> IO ()
#ccall Z3_fixedpoint_add_rule , <Z3_context> -> <Z3_fixedpoint> -> <Z3_ast> -> <Z3_symbol> -> IO ()
#ccall Z3_fixedpoint_add_fact , <Z3_context> -> <Z3_fixedpoint> -> <Z3_func_decl> -> CUInt -> Ptr CUInt -> IO ()
#ccall Z3_fixedpoint_assert , <Z3_context> -> <Z3_fixedpoint> -> <Z3_ast> -> IO ()
#ccall Z3_fixedpoint_query , <Z3_context> -> <Z3_fixedpoint> -> <Z3_ast> -> IO <Z3_lbool>
#ccall Z3_fixedpoint_query_relations , <Z3_context> -> <Z3_fixedpoint> -> CUInt -> Ptr <Z3_func_decl> -> IO <Z3_lbool>
#ccall Z3_fixedpoint_get_answer , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_ast>
#ccall Z3_fixedpoint_get_reason_unknown , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_string>
#ccall Z3_fixedpoint_update_rule , <Z3_context> -> <Z3_fixedpoint> -> <Z3_ast> -> <Z3_symbol> -> IO ()
#ccall Z3_fixedpoint_get_num_levels , <Z3_context> -> <Z3_fixedpoint> -> <Z3_func_decl> -> IO ()
#ccall Z3_fixedpoint_get_cover_delta , <Z3_context> -> <Z3_fixedpoint> -> CInt -> <Z3_func_decl> -> IO <Z3_ast>
#ccall Z3_fixedpoint_add_cover , <Z3_context> -> <Z3_fixedpoint> -> CInt -> <Z3_func_decl> -> <Z3_ast> -> IO ()
#ccall Z3_fixedpoint_get_statistics , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_stats>
#ccall Z3_fixedpoint_register_relation , <Z3_context> -> <Z3_fixedpoint> -> <Z3_func_decl> -> IO ()
#ccall Z3_fixedpoint_set_predicate_representation , <Z3_context> -> <Z3_fixedpoint> -> <Z3_func_decl> -> CUInt -> Ptr <Z3_symbol> -> IO ()
#ccall Z3_fixedpoint_get_rules , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_ast_vector>
#ccall Z3_fixedpoint_get_assertions , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_ast_vector>
#ccall Z3_fixedpoint_set_params , <Z3_context> -> <Z3_fixedpoint> -> <Z3_params> -> IO ()
#ccall Z3_fixedpoint_get_help , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_string>
#ccall Z3_fixedpoint_get_param_descrs , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_param_descrs>
#ccall Z3_fixedpoint_to_string , <Z3_context> -> <Z3_fixedpoint> -> CUInt -> Ptr <Z3_ast> -> IO <Z3_string>
#ccall Z3_fixedpoint_from_string , <Z3_context> -> <Z3_fixedpoint> -> <Z3_string> -> IO <Z3_ast_vector>
#ccall Z3_fixedpoint_from_file , <Z3_context> -> <Z3_fixedpoint> -> <Z3_string> -> IO <Z3_ast_vector>
#ccall Z3_fixedpoint_push , <Z3_context> -> <Z3_fixedpoint> -> IO ()
#ccall Z3_fixedpoint_pop , <Z3_context> -> <Z3_fixedpoint> -> IO ()
#ccall Z3_fixedpoint_reduce_assign_callback_fptr , Ptr () -> <Z3_func_decl> -> CUInt -> Ptr <Z3_ast> -> CUInt -> Ptr <Z3_ast> -> IO ()
#ccall Z3_fixedpoint_reduce_app_callback_fptr , Ptr () -> <Z3_func_decl> -> CUInt -> Ptr <Z3_ast> -> Ptr <Z3_ast> -> IO ()
#ccall Z3_fixedpoint_init , <Z3_context> -> <Z3_fixedpoint> -> Ptr () -> IO ()
#ccall Z3_fixedpoint_set_reduce_assign_callback , <Z3_context> -> <Z3_fixedpoint> -> <Z3_fixedpoint_reduce_assign_callback_fptr> -> IO ()
#ccall Z3_fixedpoint_set_reduce_app_callback , <Z3_context> -> <Z3_fixedpoint> -> <Z3_fixedpoint_reduce_app_callback_fptr> -> IO ()
#ccall Z3_mk_optimize , <Z3_context> -> IO <Z3_optimize>
#ccall Z3_optimize_inc_ref , <Z3_context> -> <Z3_optimize> -> IO ()
#ccall Z3_optimize_dec_ref , <Z3_context> -> <Z3_optimize> -> IO ()
#ccall Z3_optimize_assert , <Z3_context> -> <Z3_optimize> -> <Z3_ast> -> IO ()
#ccall Z3_optimize_assert_soft , <Z3_context> -> <Z3_optimize> -> <Z3_ast> -> <Z3_string> -> <Z3_symbol> -> IO ()
#ccall Z3_optimize_maximize , <Z3_context> -> <Z3_optimize> -> <Z3_ast> -> IO ()
#ccall Z3_optimize_minimize , <Z3_context> -> <Z3_optimize> -> <Z3_ast> -> IO ()
#ccall Z3_optimize_push , <Z3_context> -> <Z3_optimize> -> IO ()
#ccall Z3_optimize_pop , <Z3_context> -> <Z3_optimize> -> IO ()
#ccall Z3_optimize_check , <Z3_context> -> <Z3_optimize> -> IO <Z3_lbool>
#ccall Z3_optimize_get_reason_unknown , <Z3_context> -> <Z3_optimize> -> IO <Z3_string>
#ccall Z3_optimize_get_model , <Z3_context> -> <Z3_optimize> -> IO <Z3_model>
#ccall Z3_optimize_set_params , <Z3_context> -> <Z3_optimize> -> <Z3_params> -> IO ()
#ccall Z3_optimize_get_param_descrs , <Z3_context> -> <Z3_optimize> -> IO <Z3_param_descrs>
#ccall Z3_optimize_get_lower , <Z3_context> -> <Z3_optimize> -> CUInt -> IO <Z3_ast>
#ccall Z3_optimize_get_upper , <Z3_context> -> <Z3_optimize> -> CUInt -> IO <Z3_ast>
#ccall Z3_optimize_get_lower_as_vector , <Z3_context> -> <Z3_optimize> -> CUInt -> IO <Z3_ast_vector>
#ccall Z3_optimize_get_upper_as_vector , <Z3_context> -> <Z3_optimize> -> CUInt -> IO <Z3_ast_vector>
#ccall Z3_optimize_to_string , <Z3_context> -> <Z3_optimize> -> IO <Z3_string>
#ccall Z3_optimize_from_string , <Z3_context> -> <Z3_optimize> -> <Z3_string> -> IO ()
#ccall Z3_optimize_from_file , <Z3_context> -> <Z3_optimize> -> <Z3_string> -> IO ()
#ccall Z3_optimize_get_help , <Z3_context> -> <Z3_optimize> -> IO <Z3_string>
#ccall Z3_optimize_get_statistics , <Z3_context> -> <Z3_optimize> -> IO <Z3_stats>
#ccall Z3_optimize_get_assertions , <Z3_context> -> <Z3_optimize> -> IO <Z3_ast_vector>
#ccall Z3_optimize_get_objectives , <Z3_context> -> <Z3_optimize> -> IO <Z3_ast_vector>
#ccall Z3_mk_interpolant , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_interpolation_context , <Z3_config> -> IO <Z3_context>
#ccall Z3_get_interpolant , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_params> -> IO <Z3_ast_vector>
#ccall Z3_compute_interpolant , <Z3_context> -> <Z3_ast> -> <Z3_params> -> Ptr <Z3_ast_vector> -> Ptr <Z3_model> -> IO <Z3_lbool>
#ccall Z3_interpolation_profile , <Z3_context> -> IO <Z3_string>
#ccall Z3_read_interpolation_problem , <Z3_context> -> Ptr CUInt -> Ptr (Ptr <Z3_ast>) -> Ptr (Ptr CUInt) -> <Z3_string> -> <Z3_string_ptr> -> Ptr CUInt -> Ptr (Ptr <Z3_ast>) -> IO CInt
#ccall Z3_check_interpolant , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> Ptr CUInt -> Ptr <Z3_ast> -> <Z3_string_ptr> -> CUInt -> Ptr <Z3_ast> -> IO CInt
#ccall Z3_write_interpolation_problem , <Z3_context> -> CUInt -> Ptr <Z3_ast> -> Ptr CUInt -> <Z3_string> -> CUInt -> Ptr <Z3_ast> -> IO ()
#ccall Z3_mk_fpa_rounding_mode_sort , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_round_nearest_ties_to_even , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_rne , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_round_nearest_ties_to_away , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_rna , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_round_toward_positive , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_rtp , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_round_toward_negative , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_rtn , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_round_toward_zero , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_rtz , <Z3_context> -> IO <Z3_ast>
#ccall Z3_mk_fpa_sort , <Z3_context> -> CUInt -> CUInt -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_half , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_16 , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_single , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_32 , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_double , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_64 , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_quadruple , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_sort_128 , <Z3_context> -> IO <Z3_sort>
#ccall Z3_mk_fpa_nan , <Z3_context> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_inf , <Z3_context> -> <Z3_sort> -> CInt -> IO <Z3_ast>
#ccall Z3_mk_fpa_zero , <Z3_context> -> <Z3_sort> -> CInt -> IO <Z3_ast>
#ccall Z3_mk_fpa_fp , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_numeral_float , <Z3_context> -> CFloat -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_numeral_double , <Z3_context> -> CDouble -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_numeral_int , <Z3_context> -> CInt -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_numeral_int_uint , <Z3_context> -> CInt -> CInt -> CUInt -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_numeral_int64_uint64 , <Z3_context> -> CInt -> CLong -> CULong -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_abs , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_neg , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_add , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_sub , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_mul , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_div , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_fma , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_sqrt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_rem , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_round_to_integral , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_min , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_max , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_leq , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_lt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_geq , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_gt , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_eq , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_is_normal , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_is_subnormal , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_is_zero , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_is_infinite , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_is_nan , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_is_negative , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_is_positive , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_fp_bv , <Z3_context> -> <Z3_ast> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_fp_float , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_fp_real , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_fp_signed , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_fp_unsigned , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_ubv , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_sbv , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> CUInt -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_real , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_fpa_get_ebits , <Z3_context> -> <Z3_sort> -> IO ()
#ccall Z3_fpa_get_sbits , <Z3_context> -> <Z3_sort> -> IO ()
#ccall Z3_fpa_is_numeral_nan , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_fpa_is_numeral_inf , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_fpa_is_numeral_zero , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_fpa_is_numeral_normal , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_fpa_is_numeral_subnormal , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_fpa_is_numeral_positive , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_fpa_is_numeral_negative , <Z3_context> -> <Z3_ast> -> IO CInt
#ccall Z3_fpa_get_numeral_sign_bv , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_fpa_get_numeral_significand_bv , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_fpa_get_numeral_sign , <Z3_context> -> <Z3_ast> -> Ptr CInt -> IO CInt
#ccall Z3_fpa_get_numeral_significand_string , <Z3_context> -> <Z3_ast> -> IO <Z3_string>
#ccall Z3_fpa_get_numeral_significand_uint64 , <Z3_context> -> <Z3_ast> -> Ptr CULong -> IO CInt
#ccall Z3_fpa_get_numeral_exponent_string , <Z3_context> -> <Z3_ast> -> CInt -> IO <Z3_string>
#ccall Z3_fpa_get_numeral_exponent_int64 , <Z3_context> -> <Z3_ast> -> Ptr CLong -> CInt -> IO CInt
#ccall Z3_fpa_get_numeral_exponent_bv , <Z3_context> -> <Z3_ast> -> CInt -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_ieee_bv , <Z3_context> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_mk_fpa_to_fp_int_real , <Z3_context> -> <Z3_ast> -> <Z3_ast> -> <Z3_ast> -> <Z3_sort> -> IO <Z3_ast>
#ccall Z3_fixedpoint_query_from_lvl , <Z3_context> -> <Z3_fixedpoint> -> <Z3_ast> -> CUInt -> IO <Z3_lbool>
#ccall Z3_fixedpoint_get_ground_sat_answer , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_ast>
#ccall Z3_fixedpoint_get_rules_along_trace , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_ast_vector>
#ccall Z3_fixedpoint_get_rule_names_along_trace , <Z3_context> -> <Z3_fixedpoint> -> IO <Z3_symbol>
#ccall Z3_fixedpoint_add_invariant , <Z3_context> -> <Z3_fixedpoint> -> <Z3_func_decl> -> <Z3_ast> -> IO ()
#ccall Z3_fixedpoint_get_reachable , <Z3_context> -> <Z3_fixedpoint> -> <Z3_func_decl> -> IO <Z3_ast>
#ccall Z3_qe_model_project , <Z3_context> -> <Z3_model> -> CUInt -> Ptr <Z3_app> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_qe_model_project_skolem , <Z3_context> -> <Z3_model> -> CUInt -> Ptr <Z3_app> -> <Z3_ast> -> <Z3_ast_map> -> IO <Z3_ast>
#ccall Z3_model_extrapolate , <Z3_context> -> <Z3_model> -> <Z3_ast> -> IO <Z3_ast>
#ccall Z3_qe_lite , <Z3_context> -> <Z3_ast_vector> -> <Z3_ast> -> IO <Z3_ast>
