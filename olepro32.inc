;#########################################################################
;		Include files

	include windows.inc
	include kernel32.inc
	include user32.inc
	include msvcrt.inc
	include dbghelp.inc

;#########################################################################
;		Libraries

	includelib kernel32.lib
	includelib user32.lib
	includelib msvcrt.lib
	includelib dbghelp.lib

;#########################################################################
;		RadASM Add In Include

	include C:\RadASM\Masm\Inc\RadAsm.inc
	include C:\masm32\macros\macros.asm

;#########################################################################
;		VKim's Debug

	include C:\RadASM\Masm\Inc\Debug.inc
	includelib C:\RadASM\Masm\Lib\Debug.lib

	DBGWIN_DEBUG_ON = 1	; include debug info into the program
	DBGWIN_EXT_INFO = 0		; include extra debug info into the program

;#########################################################################
;		API Table

_DATA segment
	externdef c _imp__DeviceIoControl@32:ptr pr8
_DATA ends

;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; Process Environment Block (OVERLAPPED)
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

	_OVERLAPPED STRUCT				; sizeof = 14h	
		Internal						DWORD		?	; 00h
		InternalHigh					DWORD		?	; 04h
		loffset						DWORD		?	; 08h
		OffsetHigh					DWORD		?	; 0Ch
		hEvent						DWORD		?	; 10h
	_OVERLAPPED ENDS
	LPOVERLAPPED typedef PTR _OVERLAPPED

;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; Rockey4 Environment Block (ROCKEYNT)
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

	ROCKEY_DATA STRUCT				; sizeof = 28h	
		hash							DWORD		?	; 00h
		function						DWORD		?	; 04h
		handle						DWORD		?	; 08h
		lp1							DWORD		?	; 0Ch
		lp2							DWORD		?	; 10h
		p1							DWORD		?	; 14h
		p2							DWORD		?	; 18h
		p3							DWORD		?	; 1Ch
		p4							DWORD		?	; 20h
		buffer						DWORD		?	; 24h
	ROCKEY_DATA ENDS
	LPROCKEY_DATA typedef PTR ROCKEY_DATA

; 其中包括常量定义。这些常量在程序运行过程中是不能更改的。 应用程序并不需要以上所有的三个"分段"， 可以根据需要进行定义。
.CONST

	strOleIconToCursor				db	"OleIconToCursor", 0
	strOleCreatePropertyFrameIndirect	db	"OleCreatePropertyFrameIndirect", 0
	strOleCreatePropertyFrame			db	"OleCreatePropertyFrame", 0
	strOleLoadPicture					db	"OleLoadPicture", 0
	strOleCreatePictureIndirect			db	"OleCreatePictureIndirect", 0
	strOleCreateFontIndirect			db	"OleCreateFontIndirect", 0
	strOleTranslateColor				db	"OleTranslateColor", 0

	strDllCanUnloadNow				db	"DllCanUnloadNow", 0
	strDllGetClassObject				db	"DllGetClassObject", 0
	strDllRegisterServer				db	"DllRegisterServer", 0
	strDllUnregisterServer				db	"DllUnregisterServer", 0

	strProName						db	"e.exe", 0
	strKernel							db	"kernel32.dll", 0
	strCreateFile						db	"CreateFileA",0
	strDeviceIoControl					db	"DeviceIoControl", 0
	strLoadLib						db	"\olepro32.dll", 0

;#########################################################################
;		Resource ID

	ROCKEY_ENC						equ	100
	SEED_DATA						equ	101

;#########################################################################
;		Rockey 4 reference

	R4_HID							equ	6B1A5247h

	MOD_0							equ	0C43Fh
	MOD_1							equ	00D28h
	MOD_2							equ	02578h
	MOD_3							equ	0798Dh
	MOD_4							equ	0EB9Dh
	MOD_5							equ	0DF40h
	MOD_6							equ	0CB91h
	MOD_7							equ	04277h
	MOD_8							equ	0B91Fh

	MOD_9							equ	0F8ADh
	MOD_A							equ	00001h
	MOD_B							equ	00001h
	MOD_C							equ	00001h
	MOD_D							equ	0937Dh
	MOD_E							equ	00001h
	MOD_F							equ	00001h

; Pre-Define ##############################################################

	; Functions
	RY_FIND							equ	01h		; 找锁
	RY_FIND_NEXT					equ	02h		; 找下一锁
	RY_OPEN							equ	03h		; 打开锁
	RY_CLOSE						equ	04h		; 关闭锁
	RY_READ							equ	05h		; 读锁
	RY_WRITE						equ	06h		; 写锁
	RY_RANDOM						equ	07h		; 产生随机数
	RY_SEED							equ	08h		; 产生种子码
	RY_WRITE_USERID					equ	09h		; 写用户 ID
	RY_READ_USERID					equ	0Ah		; 读用户 ID
	RY_SET_MOUDLE					equ	0Bh		; 设置模块字
	RY_CHECK_MOUDLE				equ	0Ch		; 检查模块状态
	RY_WRITE_ARITHMETIC				equ	0Dh		; 写算法
	RY_CALCULATE1					equ	0Eh		; 计算 1
	RY_CALCULATE2					equ	0Fh		; 计算 2
	RY_CALCULATE3					equ	10h		; 计算 3
	RY_DECREASE						equ	11h		; 递减模块单元

	; Error Code
	ERR_SUCCESS						equ	00h		; 没有错误
	ERR_NO_PARALLEL_PORT			equ	01h		; 此机没有并口
	ERR_NO_DRIVER					equ	02h		; 没安装驱动程序
	ERR_NO_ROCKEY					equ	03h		; 并口上没有 Rockey 锁
	ERR_INVALID_PASSWORD			equ	04h		; 并口上有 Rockey 锁, 但基本密码(pass1, pass2)错
	ERR_INVALID_PASSWORD_OR_ID		equ	05h		; 错误的密码或硬件 ID
	ERR_SETID						equ	06h		; 设置硬件 ID 错
	ERR_INVALID_ADDR_OR_SIZE		equ	07h		; 读写地址或长度有误
	ERR_UNKNOWN_COMMAND		equ	08h		; 没有此命令
	ERR_NOTBELEVEL3					equ	09h		; 内部错误
	ERR_READ						equ	0Ah		; 读数据错
	ERR_WRITE						equ	0Bh		; 写数据错
	ERR_RANDOM					equ	0Ch		; 随机数错
	ERR_SEED						equ	0Dh		; 种子码错
	ERR_CALCULATE					equ	0Eh		; 计算错
	ERR_NO_OPEN					equ	0Fh		; 在操作前没有打开锁
	ERR_OPEN_OVERFLOW				equ	10h		; 打开的锁太多(>16)
	ERR_NOMORE					equ	11h		; 找不到更多的锁
	ERR_NEED_FIND					equ	12h		; 没有 Find 直接用了 FindNext
	ERR_DECREASE					equ	13h		; 递减错

	ERR_AR_BADCOMMAND			equ	14h		; 算法指令错
	ERR_AR_UNKNOWN_OPCODE		equ	15h		; 算法运算符错
	ERR_AR_WRONGBEGIN				equ	16h		; 算法第一条指令含有常数
	ERR_AR_WRONG_END				equ	17h		; 算法最后一条指令含有常数
	ERR_AR_VALUEOVERFLOW			equ	18h		; 算法中常数值 > 63
	ERR_UNKNOWN					equ	0FFFFh	; 未知错误

	ERR_RECEIVE_NULL				equ	0100h	; 接收不到
	ERR_PRNPORT_BUSY				equ	0101h	; 打印口忙

	TYPE_ROCKEY4					equ	01h		; ROCKEY4 标准并口类型
	TYPE_ROCKEY4P					equ	02h		; ROCKEY4+增强并口类型
	TYPE_ROCKEYUSB					equ	03h		; ROCKEY4 标准USB 类型
	TYPE_ROCKEYUSBP				equ	04h		; ROCKEY4+增强USB 类型
	TYPE_ROCKEYNET					equ	05h		; ROCKEY4 网络并口类型
	TYPE_ROCKEYUSBNET				equ	06h		; ROCKEY4 网络USB 类型

; 其中包括已初始化的数据。
.DATA

;#########################################################################
;		Rockey 4 reference

	Rockey_Dec						dd	20h dup(0)
	Rockey_Enc						dd	20h dup(0)
	Seed_Data						dd	130h dup(0)

	Random							dd	0

; 其中包括未初始化的数据。比如有时您仅想预先分配一些内存但并不想指定初始值。
; 使用未初始化的数据的优点是它不占据可执行文件的大小，如：若您要在 .DATA? 段中分配10，000字节的空间，您的可执行文件的大小无须增加10，000字节，而仅仅是要告诉编译器在装载可执行文件时分配所需字节。
.DATA?

	hInstance							dd	?		; Dll's module handle
	lpHandles						dd	?		; Pointer to handles struct
	lpProc							dd	?		; Pointer to proc struct
	lpData							dd	?		; Pointer to data struct
	hOut							dd	?		; Handle of output window
	IDAddIn							dd	?		; Unique ID for this AddIn

	jp_OleIconToCursor				dd	?
	jp_OleCreatePropertyFrameIndirect	dd	?
	jp_OleCreatePropertyFrame			dd	?
	jp_OleLoadPicture					dd	?
	jp_OleCreatePictureIndirect			dd	?
	jp_OleCreateFontIndirect			dd	?
	jp_OleTranslateColor				dd	?

	jp_DllCanUnloadNow				dd	?
	jp_DllGetClassObject				dd	?
	jp_DllRegisterServer				dd	?
	jp_DllUnregisterServer				dd	?

; 这是代码"分段"。
.CODE

;#########################################################################
;		Prototypes

	CheckProc PROTO
	InIATHook PROTO
	fn_CreateFileA PROTO lpFileName:LPCSTR, dwDesiredAccess:DWORD, dwShareMode:DWORD, lpSecurityAttributes:DWORD, dwCreationDisposition:DWORD, dwFlagsAndAttributes:DWORD, hTemplateFile:HANDLE
	fn_DeviceIoControl PROTO near, hDevice:HANDLE, dwIoControlCode:DWORD, lpInBuffer:ptr LPVOID, nInBufferSize:DWORD, lpOutBuffer:ptr LPVOID, nOutBufferSize:DWORD, lpBytesReturned:ptr LPDWORD, lpOverlapped:ptr LPOVERLAPPED
	LoadDebug PROTO near

	InitRockey PROTO
	ZfDecrypt PROTO

	Rockey PROTO function:DWORD, handle:ptr WORD, lp1:ptr DWORD, lp2:ptr DWORD, p1:ptr WORD, p2:ptr WORD, p3:ptr WORD, p4:ptr WORD, buffer:ptr BYTE
	RyFind PROTO near, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD, _lp1:ptr DWORD
	RyOpen PROTO near, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD, _lp1:ptr DWORD, _lp2:ptr DWORD
	RyClose PROTO _handle:ptr WORD
	RyRead PROTO near, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _buffer:ptr BYTE
	RyWrite PROTO near, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _buffer:ptr BYTE
	RyRandom PROTO near, _handle:ptr WORD, _p1:ptr WORD
	RySeed PROTO near, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD, _lp2:ptr DWORD
	RyCalculate1 PROTO _handle:ptr WORD, _lp1:ptr DWORD, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD
	RyCalculate3 PROTO _handle:ptr WORD, _lp1:ptr DWORD, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	CALC_00 PROTO near, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD
	CALC_04 PROTO near, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD
	CALC_10_OR_28 PROTO near, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD
	CALC_20 PROTO near, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	EncryptName PROTO near, lpProcName:LPCSTR

;#########################################################################
;	A=A^G, B=B|B, C=C|C, D=D|D	G=MOD_X
CALC_00 proc near uses ecx edx ebx esi, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	mov eax, _p1
	mov ecx, _p2
	mov edx, _p3
	mov ebx, _p4
	mov esi, _lp2

	; A=A^G
	.if word ptr [esi] == 00h
		xor word ptr [eax], MOD_0
	.elseif word ptr [esi] == 01h
		xor word ptr [eax], MOD_1
	.elseif word ptr [esi] == 02h
		xor word ptr [eax], MOD_2
	.elseif word ptr [esi] == 03h
		xor word ptr [eax], MOD_3
	.elseif word ptr [esi] == 04h
		xor word ptr [eax], MOD_4
	.elseif word ptr [esi] == 05h
		xor word ptr [eax], MOD_5
	.elseif word ptr [esi] == 06h
		xor word ptr [eax], MOD_6
	.elseif word ptr [esi] == 07h
		xor word ptr [eax], MOD_7
	.elseif word ptr [esi] == 08h
		xor word ptr [eax], MOD_8
	.elseif word ptr [esi] == 09h
		xor word ptr [eax], MOD_9
	.elseif word ptr [esi] == 0Ah
		xor word ptr [eax], MOD_A
	.elseif word ptr [esi] == 0Bh
		xor word ptr [eax], MOD_B
	.elseif word ptr [esi] == 0Ch
		xor word ptr [eax], MOD_C
	.elseif word ptr [esi] == 0Dh
		xor word ptr [eax], MOD_D
	.elseif word ptr [esi] == 0Eh
		xor word ptr [eax], MOD_E
	.elseif word ptr [esi] == 0Fh
		xor word ptr [eax], MOD_F
	.endif

	ret
CALC_00 endp

;	A=B^H, B=A^G, C=C|C, D=D|D	G=MOD_X
CALC_04 proc near uses ecx edx ebx esi edi, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	mov edi, _p1
	mov ecx, _p2
	mov edx, _p3
	mov ebx, _p4
	mov esi, _lp2

	; A=B^H
	movzx eax, word ptr [ecx]
	xchg al, ah
	mov bx, 190Dh
	mul bx
	add ax, 10DCh
	xor ax, word ptr [ecx]
	mov word ptr [edi], ax

	; B=A^G
	.if word ptr [esi] == 00h
		xor ax, MOD_0
	.elseif word ptr [esi] == 01h
		xor ax, MOD_1
	.elseif word ptr [esi] == 02h
		xor ax, MOD_2
	.elseif word ptr [esi] == 03h
		xor ax, MOD_3
	.elseif word ptr [esi] == 04h
		xor ax, MOD_4
	.elseif word ptr [esi] == 05h
		xor ax, MOD_5
	.elseif word ptr [esi] == 06h
		xor ax, MOD_6
	.elseif word ptr [esi] == 07h
		xor ax, MOD_7
	.elseif word ptr [esi] == 08h
		xor ax, MOD_8
	.elseif word ptr [esi] == 09h
		xor ax, MOD_9
	.elseif word ptr [esi] == 0Ah
		xor ax, MOD_A
	.elseif word ptr [esi] == 0Bh
		xor ax, MOD_B
	.elseif word ptr [esi] == 0Ch
		xor ax, MOD_C
	.elseif word ptr [esi] == 0Dh
		xor ax, MOD_D
	.elseif word ptr [esi] == 0Eh
		xor ax, MOD_E
	.elseif word ptr [esi] == 0Fh
		xor ax, MOD_F
	.endif
	mov word ptr [ecx], ax

	ret
CALC_04 endp

;	A=A^G, B=B^G, C=C|C, D=D|D	G=MOD_X
CALC_10_OR_28 proc near uses ecx edx ebx esi, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	mov eax, _p1
	mov ecx, _p2
	mov edx, _p3
	mov ebx, _p4
	mov esi, _lp2

	; A=A^G, B=B^G
	.if word ptr [esi] == 00h
		xor word ptr [eax], MOD_2
		xor word ptr [ecx], MOD_2
	.elseif word ptr [esi] == 01h
		xor word ptr [eax], MOD_3
		xor word ptr [ecx], MOD_3
	.elseif word ptr [esi] == 02h
		xor word ptr [eax], MOD_4
		xor word ptr [ecx], MOD_4
	.elseif word ptr [esi] == 03h
		xor word ptr [eax], MOD_5
		xor word ptr [ecx], MOD_5
	.elseif word ptr [esi] == 04h
		xor word ptr [eax], MOD_6
		xor word ptr [ecx], MOD_6
	.elseif word ptr [esi] == 05h
		xor word ptr [eax], MOD_7
		xor word ptr [ecx], MOD_7
	.elseif word ptr [esi] == 06h
		xor word ptr [eax], MOD_8
		xor word ptr [ecx], MOD_8
	.elseif word ptr [esi] == 07h
		xor word ptr [eax], MOD_9
		xor word ptr [ecx], MOD_9
	.elseif word ptr [esi] == 08h
		xor word ptr [eax], MOD_A
		xor word ptr [ecx], MOD_A
	.elseif word ptr [esi] == 09h
		xor word ptr [eax], MOD_B
		xor word ptr [ecx], MOD_B
	.elseif word ptr [esi] == 0Ah
		xor word ptr [eax], MOD_C
		xor word ptr [ecx], MOD_C
	.elseif word ptr [esi] == 0Bh
		xor word ptr [eax], MOD_D
		xor word ptr [ecx], MOD_D
	.elseif word ptr [esi] == 0Ch
		xor word ptr [eax], MOD_E
		xor word ptr [ecx], MOD_E
	.elseif word ptr [esi] == 0Dh
		xor word ptr [eax], MOD_F
		xor word ptr [ecx], MOD_F
	.elseif word ptr [esi] == 0Eh
		xor word ptr [eax], MOD_0
		xor word ptr [ecx], MOD_0
	.elseif word ptr [esi] == 0Fh
		xor word ptr [eax], MOD_1
		xor word ptr [ecx], MOD_1
	.endif

	ret
CALC_10_OR_28 endp

;	A=A|A, B=B|B, C=C|C, D=D|D	G=MOD_X
CALC_20 proc near uses ecx edx ebx esi, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	; A=A|A, B=B|B, C=C|C, D=D|D
	mov eax, _p1
	mov ecx, _p2
	mov edx, _p3
	mov ebx, _p4
	mov esi, _lp2

	ret
CALC_20 endp

;#########################################################################

EncryptName proc near uses ecx edx, lpProcName:LPCSTR

	;DebugOut "EncryptName : [lpProcName][%hs]", lpProcName
	xor eax, eax
	mov ecx, lpProcName
	.while byte ptr [ecx] != 0
		mov dl, [ecx]
		movsx edx, dl
		or edx, 20h
		add eax, edx
		rol eax, 0Dh
		inc ecx
	.endw

	ret
EncryptName endp

;#########################################################################