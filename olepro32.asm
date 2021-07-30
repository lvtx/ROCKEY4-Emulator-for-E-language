;#########################################################################
;		Assembler directives

.486
.model flat, stdcall
option casemap:none

;#########################################################################
;		Include file

include olepro32.inc
include PE.inc

.code

;#########################################################################
;		Common AddIn Procedures

DllEntry proc hInst:HINSTANCE, reason:DWORD, reserved1:DWORD

	mov eax, hInst
	mov hInstance, eax
	.if reason == DLL_PROCESS_ATTACH
		invoke LoadDebug
		invoke CheckProc
	.elseif reason == DLL_PROCESS_DETACH
	.elseif reason == DLL_THREAD_ATTACH
	.elseif reason == DLL_THREAD_DETACH
	.endif

	mov eax, TRUE
	ret
DllEntry Endp

CheckProc proc
LOCAL hSnapShot:DWORD
LOCAL pModule:MODULEENTRY32

	pushad
	mov hSnapShot, rv(CreateToolhelp32Snapshot, TH32CS_SNAPALL, rv(GetCurrentProcessId))
	.if hSnapShot != INVALID_HANDLE_VALUE
		invoke RtlZeroMemory, addr pModule, sizeof pModule
		mov pModule.dwSize, sizeof pModule

		invoke Module32First, hSnapShot, addr pModule
		.while eax != 0
			.if !rv(lstrcmpi, addr pModule.szModule, addr strProName)
				invoke InitRockey
				invoke InIATHook
				.break
			.endif
			invoke Module32Next, hSnapShot, addr pModule
		.endw

		invoke CloseHandle, hSnapShot
	.endif
	popad

	ret
CheckProc endp

InIATHook proc near uses ecx edx ebx esi edi
LOCAL hModule:DWORD
LOCAL lpAddress:DWORD
LOCAL dwSize:DWORD
LOCAL lpflOldProtect:DWORD

	mov hModule, rv(GetModuleHandle, addr strProName)
	.if hModule
		mov edi, eax
		; 检测PE文件是否有效
		assume edi: ptr _IMAGE_DOS_HEADER
		; 调整esi指针指向PE文件头
		mov esi, [edi].e_lfanew
		add esi, edi
		assume esi: ptr _IMAGE_NT_HEADERS

		mov eax, [esi].OptionalHeader.DataDirectory[sizeof _IMAGE_DATA_DIRECTORY*IMAGE_DIRECTORY_ENTRY_IAT].VirtualAddress
		mov edx, [esi].OptionalHeader.DataDirectory[sizeof _IMAGE_DATA_DIRECTORY*IMAGE_DIRECTORY_ENTRY_IAT].isize
		add eax, edi
		mov lpAddress, eax
		mov dwSize, edx

		invoke VirtualProtect, lpAddress, dwSize, PAGE_READWRITE, addr lpflOldProtect

		mov esi, [esi].OptionalHeader.DataDirectory[sizeof _IMAGE_DATA_DIRECTORY*IMAGE_DIRECTORY_ENTRY_IMPORT].VirtualAddress
		add esi, edi
		assume esi: ptr IMAGE_IMPORT_DESCRIPTOR
		.while [esi].FirstThunk != 0
			mov ecx, [esi].Name1
			add ecx, edi
			invoke EncryptName, ecx
			.if eax == 0D0ED5937h				; KERNEL32.dll
				mov ebx, [esi].Characteristics
				mov esi, [esi].FirstThunk
				add ebx, edi
				add esi, edi
				assume ebx: ptr IMAGE_THUNK_DATA
				.while [ebx].u1.Function != 0
					mov eax, [ebx].u1.Function
					assume eax: ptr IMAGE_IMPORT_BY_NAME
					lea eax, [eax].Name1
					assume eax: nothing
					add eax, edi
					invoke EncryptName, eax
					.if eax == 47877999h			; CreateFileA
						;DebugOut "[InIATHook] : [Hook][CreateFileA]"
						mov dword ptr [esi], offset fn_CreateFileA
					.elseif eax == 91FC599Bh		; DeviceIoControl
						;DebugOut "[InIATHook] : [Hook][DeviceIoControl]"
						mov dword ptr [esi], offset fn_DeviceIoControl
					.endif
					add ebx, sizeof IMAGE_THUNK_DATA
					add esi, sizeof IMAGE_THUNK_DATA
				.endw
				assume ebx: nothing
				.break
			.endif
			add esi, sizeof IMAGE_IMPORT_DESCRIPTOR
		.endw
		assume esi: nothing

		invoke VirtualProtect, lpAddress, dwSize, lpflOldProtect, addr lpflOldProtect
	.endif
	assume edi: nothing

	ret
InIATHook endp

InitRockey proc
LOCAL hRsrc:DWORD, dwSize:DWORD, hResData:DWORD, lpRes:DWORD

	pushad
	invoke FindResource, hInstance, ROCKEY_ENC, RT_RCDATA	; 查找ASM资源
	mov hRsrc, eax
	invoke SizeofResource, hInstance, hRsrc					; 获取资源长度
	mov dwSize, eax
	invoke LoadResource, hInstance, hRsrc					; 装载资源
	mov hResData, eax
	invoke LockResource, hResData							; 锁定它
	mov lpRes, eax
	invoke RtlMoveMemory, addr Rockey_Enc, lpRes, dwSize

	invoke FindResource, hInstance, SEED_DATA, RT_RCDATA		; 查找ASM资源
	mov hRsrc, eax
	invoke SizeofResource, hInstance, hRsrc					; 获取资源长度
	mov dwSize, eax
	invoke LoadResource, hInstance, hRsrc					; 装载资源
	mov hResData, eax
	invoke LockResource, hResData							; 锁定它
	mov lpRes, eax
	invoke RtlMoveMemory, addr Seed_Data, lpRes, dwSize

	invoke ZfDecrypt
	popad

	ret
	
InitRockey endp

ZfDecrypt proc near uses ecx edx ebx esi edi
LOCAL Control[80h]:BYTE, DecAddr:DWORD, DecLen:DWORD

	invoke RtlZeroMemory, addr Control, sizeof Control
	invoke crt_srand, 2537h
	xor edi, edi
	.repeat
		invoke crt_rand
		cdq
		mov ecx, 100h
		idiv ecx
		mov byte ptr [Control+edi], dl
		inc edi
	.until edi >= 80h

	mov eax, offset Rockey_Enc
	mov DecAddr, eax
	mov DecLen, 78h
	xor esi, esi

	.repeat
		mov eax, esi
		mov ecx, 80h
		cdq
		idiv ecx
		mov eax, DecAddr
		push 8
		pop ecx
		mov bl, byte ptr [Control+edx]
		xor bl, byte ptr [eax+esi]
		mov eax, esi
		cdq
		idiv ecx
		mov al, bl
		sub ecx, edx
		shl al, cl
		mov cl, dl
		shr bl, cl
		mov ecx, DecAddr
		add al, bl
		mov byte ptr [ecx+esi], al	
		inc esi
	.until esi >= DecLen

	ret
ZfDecrypt endp

fn_CreateFileA proc lpFileName:LPCSTR, dwDesiredAccess:DWORD, dwShareMode:DWORD, lpSecurityAttributes:DWORD, dwCreationDisposition:DWORD, dwFlagsAndAttributes:DWORD, hTemplateFile:HANDLE

	; --------------------------------------------------
	; lpFileName
	; EncryptName("\\.\ROCKEYNT") = 0635F01Bh
	invoke EncryptName, lpFileName

	; 判断是否 ROCKEY4 调用
	; \\.\ROCKEYNT
	.if eax == 0635F01Bh && dwDesiredAccess == 0C0000000h && dwCreationDisposition == OPEN_EXISTING && dwFlagsAndAttributes == 00000080h
		mov eax, R4_HID
	.else
		invoke CreateFileA, lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile
	.endif

	ret
fn_CreateFileA endp

;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; 参数：
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; hDevice [in]
; 	需要执行操作的设备句柄。该设备通常是卷，目录，文件或流，使用 CreateFile 函数打开获取设备句柄。具体的见备注
; dwIoControlCode [in]
; 	操作的控制代码，该值标识要执行的特定操作以及执行该操作的设备的类型，有关控制代码的列表，请参考备注。每个控制代码的文档都提供了lpInBuffer，nInBufferSize，lpOutBuffer和nOutBufferSize参数的使用细节。
; lpInBuffer [in, optional]
; 	（可选）指向输入缓冲区的指针。这些数据的格式取决于dwIoControlCode参数的值。如果dwIoControlCode指定不需要输入数据的操作，则此参数可以为NULL。
; nInBufferSize [in]
; 	输入缓冲区以字节为单位的大小。单位为字节。
; lpOutBuffer [out, optional]
; 	（可选）指向输出缓冲区的指针。这些数据的格式取决于dwIoControlCode参数的值。如果dwIoControlCode指定不返回数据的操作，则此参数可以为NULL。
; nOutBufferSize [in]
; 	输出缓冲区以字节为单位的大小。单位为字节。
; lpBytesReturned [out, optional]
; 	（可选）指向一个变量的指针，该变量接收存储在输出缓冲区中的数据的大小。如果输出缓冲区太小，无法接收任何数据，则GetLastError返回ERROR_INSUFFICIENT_BUFFER,错误代码122(0x7a)，此时lpBytesReturned是零。
; 	如果输出缓冲区太小而无法保存所有数据，但可以保存一些条目，某些驱动程序将返回尽可能多的数据,在这种情况下，调用失败，GetLastError返回ERROR_MORE_DATA,错误代码234，lpBytesReturned指示接收到的数据量。您的应用程序应该再次使用相同的操作调用DeviceIoControl，指定一个新的起点。
; 	如果lpOverlapped为NULL，则lpBytesReturned不能为NULL。 即使操作没有返回输出数据并且lpOutBuffer为NULL，DeviceIoControl也会使用lpBytesReturned。在这样的操作之后，lpBytesReturned的值是没有意义的。
; 	如果lpOverlapped不为NULL，则lpBytesReturned可以为NULL。 如果此参数不为NULL并且操作返回数据，则在重叠操作完成之前，lpBytesReturned是无意义的。要检索返回的字节数，请调用GetOverlappedResult,如果hDevice与I / O完成端口相关联，则可以检索通过调用GetQueuedCompletionStatus返回的字节数。 
; lpOverlapped [in, out, optional]
; 	（可选）指向OVERLAPPED结构的指针,
; 	如果在未指定FILE_FLAG_OVERLAPPED的情况下打开hDevice，则忽略lpOverlapped。
; 	如果使用FILE_FLAG_OVERLAPPED标志打开hDevice，则该操作将作为重叠（异步）操作执行。在这种情况下，lpOverlapped必须指向包含事件对象句柄的有效OVERLAPPED结构。 否则，该功能将以不可预知的方式失败。
; 	对于重叠操作，DeviceIoControl会立即返回，并在操作完成时通知事件对象。 否则，该功能在操作完成或发生错误之前不会返回。
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; 返回值:
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; 	如果操作成功完成，DeviceIoControl将返回一个非零值。
; 	如果操作失败或正在等待，则DeviceIoControl返回零。 要获得扩展的错误信息，请调用GetLastError。
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

fn_DeviceIoControl proc near uses ecx, hDevice:HANDLE, dwIoControlCode:DWORD, lpInBuffer:ptr LPVOID, nInBufferSize:DWORD, lpOutBuffer:ptr LPVOID, nOutBufferSize:DWORD, lpBytesReturned:ptr LPDWORD, lpOverlapped:ptr LPOVERLAPPED

	; 判断是否 ROCKEY4 调用
	.if dwIoControlCode == 0A410E400h
		; --------------------------------------------------
		; lpInBuffer 为加密后数据
		; ry_Encrypt(lpInBuffer, OriginBuffer)
		;mov ecx, lpInBuffer
		; --------------------------------------------------
		; 这里懒得写解密过程了，直接硬跳指针取值算了
		lea ecx, [ebp+2B4h]
		; --------------------------------------------------
		assume ecx: ptr ROCKEY_DATA
		invoke Rockey, [ecx].function, [ecx].handle, [ecx].lp1, [ecx].lp2, [ecx].p1, [ecx].p2, [ecx].p3, [ecx].p4, [ecx].buffer
		assume ecx: nothing

		.if eax == TRUE
			mov eax, lpOutBuffer
			mov word ptr [eax], 0	; ERR_SUCCESS
		.endif

		mov eax, TRUE
	.else
		invoke DeviceIoControl, hDevice, dwIoControlCode, lpInBuffer, nInBufferSize, lpOutBuffer, nOutBufferSize, lpBytesReturned, lpOverlapped
	.endif

	ret
fn_DeviceIoControl endp

Rockey proc function:DWORD, handle:ptr WORD, lp1:ptr DWORD, lp2:ptr DWORD, p1:ptr WORD, p2:ptr WORD, p3:ptr WORD, p4:ptr WORD, buffer:ptr BYTE

	;add ebp, 2B8h
	.if function == RY_FIND
		invoke RyFind, p1, p2, p3, p4, lp1
	.elseif function == RY_OPEN
		invoke RyOpen, handle, p1, p2, p3, p4, lp1, lp2
	.elseif function == RY_CLOSE
		invoke RyClose, handle
	.elseif function == RY_READ
		invoke RyRead, handle, p1, p2, buffer
	.elseif function == RY_WRITE
		invoke RyWrite, handle, p1, p2, buffer
	.elseif function == RY_RANDOM
		invoke RyRandom, handle, p1
	.elseif function == RY_SEED
		invoke RySeed, handle, p1, p2, p3, p4, lp2
	.elseif function == RY_CALCULATE1
		invoke RyCalculate1, handle, lp1, lp2, p1, p2, p3, p4
	.elseif function == RY_CALCULATE3
		invoke RyCalculate3, handle, lp1, lp2, p1, p2, p3, p4
	.endif
	;sub ebp, 2B8h

	ret
Rockey endp

RyFind proc near uses ecx edx ebx esi, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD, _lp1:ptr DWORD

	mov eax, _p1
	mov ecx, _p2
	mov edx, _p3
	mov ebx, _p4
	mov esi, _lp1

	.if word ptr [eax] == 0BFEFh && word ptr [ecx] == 04FBCh && word ptr [edx] == 0 && word ptr [ebx] == 0
		mov dword ptr [esi], R4_HID
		mov eax, TRUE
	.else
		mov eax, FALSE
	.endif

	ret
RyFind endp

RyOpen proc near uses ecx edx ebx esi edi, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD, _lp1:ptr DWORD, _lp2:ptr DWORD

	mov eax, _p1
	mov ecx, _p2
	mov edx, _p3
	mov ebx, _p4
	mov esi, _lp1
	mov edi, _lp2

	.if word ptr [eax] == 0BFEFh && word ptr [ecx] == 04FBCh && word ptr [edx] == 0 && word ptr [ebx] == 0\
		&& dword ptr [esi] == R4_HID
		mov eax, _handle
		mov dword ptr [eax], R4_HID
		mov dword ptr [edi], TYPE_ROCKEYUSBP
		mov eax, TRUE
	.else
		mov eax, FALSE
	.endif

	ret
RyOpen endp

RyClose proc _handle:ptr WORD

	mov eax, TRUE
	ret
RyClose endp

RyRead proc near uses ecx esi edi, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _buffer:ptr BYTE

	mov eax, _p1
	mov ecx, _p2
	mov edi, _buffer

	mov esi, [eax]
	add esi, offset Rockey_Enc
	cld
	mov ecx, dword ptr [ecx]
	rep movsb

	mov eax, TRUE
	ret
RyRead endp

RyWrite proc near uses ecx esi edi, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _buffer:ptr BYTE

	mov eax, _p1
	mov ecx, _p2
	mov esi, _buffer

	mov edi, [eax]
	add edi, offset Rockey_Enc
	cld
	mov ecx, dword ptr [ecx]
	rep movsb

	mov eax, TRUE
	ret
RyWrite endp

RyRandom proc near uses ecx ebx esi, _handle:ptr WORD, _p1:ptr WORD

	mov ebx, _p1

	.if !Random
		mov ax, [ebx]
		invoke crt_srand, ax
		invoke crt_rand
		and eax, 64h
		mov ecx, 03h
		mul cl

		mov esi, dword ptr [eax*4+Seed_Data]
		shr esi, 10h
		mov word ptr [ebx], si
		mov Random, eax
	.else
		mov eax, Random
		mov si, word ptr [eax*4+Seed_Data]
		mov word ptr [ebx], si
		mov Random, 0
	.endif

	mov eax, TRUE
	ret
RyRandom endp

RySeed proc near uses ecx edx ebx esi edi, _handle:ptr WORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD, _lp2:ptr DWORD

	mov eax, _lp2

	mov eax, [eax]
	mov edi, offset Seed_Data
	cld
	mov ecx, 12Eh
	repnz scasd
	mov edi, 12Eh
	sub edi, ecx

	mov eax, _p1
	mov ecx, _p2
	mov edx, _p3
	mov ebx, _p4

	mov esi, dword ptr [edi*4+Seed_Data]
	shr esi, 10h
	mov word ptr [eax], si
	mov si, word ptr [edi*4+Seed_Data]
	mov word ptr [ecx], si
	mov esi, dword ptr [edi*4+Seed_Data+4]
	shr esi, 10h
	mov word ptr [edx], si
	mov si, word ptr [edi*4+Seed_Data+4]
	mov word ptr [ebx], si

	mov eax, TRUE
	ret
RySeed endp

RyCalculate1 proc _handle:ptr WORD, _lp1:ptr DWORD, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	mov eax, _lp1

	.if word ptr [eax] == 00h
		invoke CALC_00, _lp2, _p1, _p2, _p3, _p4
		mov eax, TRUE
	.elseif word ptr [eax] == 04h
		invoke CALC_04, _lp2, _p1, _p2, _p3, _p4
		mov eax, TRUE
	.else
		mov eax, FALSE
	.endif

	ret
RyCalculate1 endp

RyCalculate3 proc _handle:ptr WORD, _lp1:ptr DWORD, _lp2:ptr DWORD, _p1:ptr WORD, _p2:ptr WORD, _p3:ptr WORD, _p4:ptr WORD

	mov eax, _lp1

	.if word ptr [eax] == 10h
		invoke CALC_10_OR_28, _lp2, _p1, _p2, _p3, _p4
		mov eax, TRUE
	.elseif word ptr [eax] == 20h
		invoke CALC_20, _lp2, _p1, _p2, _p3, _p4
		mov eax, TRUE
	.elseif word ptr [eax] == 28h
		invoke CALC_10_OR_28, _lp2, _p1, _p2, _p3, _p4
		mov eax, TRUE
	.else
		mov eax, FALSE
	.endif

	ret
RyCalculate3 endp

LoadDebug proc near uses ecx edx ebx esi edi
LOCAL LibPath[MAX_PATH]:BYTE
LOCAL LibID:DWORD

	invoke GetSystemDirectory, addr LibPath, MAX_PATH
	lea ebx, LibPath
	add eax, ebx

	mov edi, eax
	mov esi, offset strLoadLib
	mov ecx, 0Eh
	rep movsb

	invoke LoadLibrary, addr LibPath
	.if eax != 0
		mov LibID, eax
		invoke GetProcAddress, LibID, addr strOleIconToCursor
		mov jp_OleIconToCursor, eax
		invoke GetProcAddress, LibID, addr strOleCreatePropertyFrameIndirect
		mov jp_OleCreatePropertyFrameIndirect, eax
		invoke GetProcAddress, LibID, addr strOleCreatePropertyFrame
		mov jp_OleCreatePropertyFrame, eax
		invoke GetProcAddress, LibID, addr strOleLoadPicture
		mov jp_OleLoadPicture, eax
		invoke GetProcAddress, LibID, addr strOleCreatePictureIndirect
		mov jp_OleCreatePictureIndirect, eax
		invoke GetProcAddress, LibID, addr strOleCreateFontIndirect
		mov jp_OleCreateFontIndirect, eax
		invoke GetProcAddress, LibID, addr strOleTranslateColor
		mov jp_OleTranslateColor, eax
		
		invoke GetProcAddress, LibID, addr strDllCanUnloadNow
		mov jp_DllCanUnloadNow, eax
		invoke GetProcAddress, LibID, addr strDllGetClassObject
		mov jp_DllGetClassObject, eax
		invoke GetProcAddress, LibID, addr strDllRegisterServer
		mov jp_DllRegisterServer, eax
		invoke GetProcAddress, LibID, addr strDllUnregisterServer
		mov jp_DllUnregisterServer, eax
	.endif

	ret
LoadDebug endp

OleIconToCursor proc
	jmp jp_OleIconToCursor
OleIconToCursor endp

OleCreatePropertyFrameIndirect proc
	jmp jp_OleCreatePropertyFrameIndirect
OleCreatePropertyFrameIndirect endp

OleCreatePropertyFrame proc
	jmp jp_OleCreatePropertyFrame
OleCreatePropertyFrame endp

OleLoadPicture proc
	jmp jp_OleLoadPicture
OleLoadPicture endp

OleCreatePictureIndirect proc
	jmp jp_OleCreatePictureIndirect
OleCreatePictureIndirect endp

OleCreateFontIndirect proc
	jmp jp_OleCreateFontIndirect
OleCreateFontIndirect endp

OleTranslateColor proc
	jmp jp_OleTranslateColor
OleTranslateColor endp

DllCanUnloadNow proc
	jmp jp_DllCanUnloadNow
DllCanUnloadNow endp

DllGetClassObject proc
	jmp jp_DllGetClassObject
DllGetClassObject endp

DllRegisterServer proc
	jmp jp_DllRegisterServer
DllRegisterServer endp

DllUnregisterServer proc
	jmp jp_DllUnregisterServer
DllUnregisterServer endp

;#########################################################################

End DllEntry
