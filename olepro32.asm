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
		; ���PE�ļ��Ƿ���Ч
		assume edi: ptr _IMAGE_DOS_HEADER
		; ����esiָ��ָ��PE�ļ�ͷ
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
	invoke FindResource, hInstance, ROCKEY_ENC, RT_RCDATA	; ����ASM��Դ
	mov hRsrc, eax
	invoke SizeofResource, hInstance, hRsrc					; ��ȡ��Դ����
	mov dwSize, eax
	invoke LoadResource, hInstance, hRsrc					; װ����Դ
	mov hResData, eax
	invoke LockResource, hResData							; ������
	mov lpRes, eax
	invoke RtlMoveMemory, addr Rockey_Enc, lpRes, dwSize

	invoke FindResource, hInstance, SEED_DATA, RT_RCDATA		; ����ASM��Դ
	mov hRsrc, eax
	invoke SizeofResource, hInstance, hRsrc					; ��ȡ��Դ����
	mov dwSize, eax
	invoke LoadResource, hInstance, hRsrc					; װ����Դ
	mov hResData, eax
	invoke LockResource, hResData							; ������
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

	; �ж��Ƿ� ROCKEY4 ����
	; \\.\ROCKEYNT
	.if eax == 0635F01Bh && dwDesiredAccess == 0C0000000h && dwCreationDisposition == OPEN_EXISTING && dwFlagsAndAttributes == 00000080h
		mov eax, R4_HID
	.else
		invoke CreateFileA, lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile
	.endif

	ret
fn_CreateFileA endp

;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; ������
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; hDevice [in]
; 	��Ҫִ�в������豸��������豸ͨ���Ǿ�Ŀ¼���ļ�������ʹ�� CreateFile �����򿪻�ȡ�豸���������ļ���ע
; dwIoControlCode [in]
; 	�����Ŀ��ƴ��룬��ֵ��ʶҪִ�е��ض������Լ�ִ�иò������豸�����ͣ��йؿ��ƴ�����б���ο���ע��ÿ�����ƴ�����ĵ����ṩ��lpInBuffer��nInBufferSize��lpOutBuffer��nOutBufferSize������ʹ��ϸ�ڡ�
; lpInBuffer [in, optional]
; 	����ѡ��ָ�����뻺������ָ�롣��Щ���ݵĸ�ʽȡ����dwIoControlCode������ֵ�����dwIoControlCodeָ������Ҫ�������ݵĲ�������˲�������ΪNULL��
; nInBufferSize [in]
; 	���뻺�������ֽ�Ϊ��λ�Ĵ�С����λΪ�ֽڡ�
; lpOutBuffer [out, optional]
; 	����ѡ��ָ�������������ָ�롣��Щ���ݵĸ�ʽȡ����dwIoControlCode������ֵ�����dwIoControlCodeָ�����������ݵĲ�������˲�������ΪNULL��
; nOutBufferSize [in]
; 	������������ֽ�Ϊ��λ�Ĵ�С����λΪ�ֽڡ�
; lpBytesReturned [out, optional]
; 	����ѡ��ָ��һ��������ָ�룬�ñ������մ洢������������е����ݵĴ�С��������������̫С���޷������κ����ݣ���GetLastError����ERROR_INSUFFICIENT_BUFFER,�������122(0x7a)����ʱlpBytesReturned���㡣
; 	������������̫С���޷������������ݣ������Ա���һЩ��Ŀ��ĳЩ�������򽫷��ؾ����ܶ������,����������£�����ʧ�ܣ�GetLastError����ERROR_MORE_DATA,�������234��lpBytesReturnedָʾ���յ���������������Ӧ�ó���Ӧ���ٴ�ʹ����ͬ�Ĳ�������DeviceIoControl��ָ��һ���µ���㡣
; 	���lpOverlappedΪNULL����lpBytesReturned����ΪNULL�� ��ʹ����û�з���������ݲ���lpOutBufferΪNULL��DeviceIoControlҲ��ʹ��lpBytesReturned���������Ĳ���֮��lpBytesReturned��ֵ��û������ġ�
; 	���lpOverlapped��ΪNULL����lpBytesReturned����ΪNULL�� ����˲�����ΪNULL���Ҳ����������ݣ������ص��������֮ǰ��lpBytesReturned��������ġ�Ҫ�������ص��ֽ����������GetOverlappedResult,���hDevice��I / O��ɶ˿������������Լ���ͨ������GetQueuedCompletionStatus���ص��ֽ����� 
; lpOverlapped [in, out, optional]
; 	����ѡ��ָ��OVERLAPPED�ṹ��ָ��,
; 	�����δָ��FILE_FLAG_OVERLAPPED������´�hDevice�������lpOverlapped��
; 	���ʹ��FILE_FLAG_OVERLAPPED��־��hDevice����ò�������Ϊ�ص����첽������ִ�С�����������£�lpOverlapped����ָ������¼�����������ЧOVERLAPPED�ṹ�� ���򣬸ù��ܽ��Բ���Ԥ֪�ķ�ʽʧ�ܡ�
; 	�����ص�������DeviceIoControl���������أ����ڲ������ʱ֪ͨ�¼����� ���򣬸ù����ڲ�����ɻ�������֮ǰ���᷵�ء�
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; ����ֵ:
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
; 	��������ɹ���ɣ�DeviceIoControl������һ������ֵ��
; 	�������ʧ�ܻ����ڵȴ�����DeviceIoControl�����㡣 Ҫ�����չ�Ĵ�����Ϣ�������GetLastError��
;:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

fn_DeviceIoControl proc near uses ecx, hDevice:HANDLE, dwIoControlCode:DWORD, lpInBuffer:ptr LPVOID, nInBufferSize:DWORD, lpOutBuffer:ptr LPVOID, nOutBufferSize:DWORD, lpBytesReturned:ptr LPDWORD, lpOverlapped:ptr LPOVERLAPPED

	; �ж��Ƿ� ROCKEY4 ����
	.if dwIoControlCode == 0A410E400h
		; --------------------------------------------------
		; lpInBuffer Ϊ���ܺ�����
		; ry_Encrypt(lpInBuffer, OriginBuffer)
		;mov ecx, lpInBuffer
		; --------------------------------------------------
		; ��������д���ܹ����ˣ�ֱ��Ӳ��ָ��ȡֵ����
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
