// Vision Studio: per-application audio capture helper.
//
// Captures the sound ONE program (and the programs it started) is playing, with no virtual audio cable,
// using Windows' "process loopback" capture (the same method Microsoft's ApplicationLoopback sample shows).
// It writes raw audio to standard output: 44100 Hz, 16-bit, 2 channels, little-endian, no header.
// Messages for Vision Studio go to standard error, one per line, starting with OK or ERROR.
//
//   vs_appcapture.exe <process id> [include|exclude]
//
// include (default) captures only that process tree; exclude captures everything except it.
// It exits when its standard output is closed, so it never outlives Vision Studio.

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <initguid.h>
#include <audioclient.h>
#include <audioclientactivationparams.h>
#include <mmdeviceapi.h>
#include <propidl.h>
#include <io.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#pragma comment(lib, "ole32.lib")
#pragma comment(lib, "mmdevapi.lib")

class ActivateHandler : public IActivateAudioInterfaceCompletionHandler, public IAgileObject
{
public:
    ActivateHandler() : refs_(1), done_(CreateEventW(nullptr, TRUE, FALSE, nullptr)), result_(E_FAIL), client_(nullptr) {}
    ~ActivateHandler() { if (done_) CloseHandle(done_); if (client_) client_->Release(); }

    // IUnknown
    STDMETHODIMP QueryInterface(REFIID riid, void **object) override
    {
        if (riid == __uuidof(IUnknown) || riid == __uuidof(IActivateAudioInterfaceCompletionHandler))
            *object = static_cast<IActivateAudioInterfaceCompletionHandler *>(this);
        else if (riid == __uuidof(IAgileObject))
            *object = static_cast<IAgileObject *>(this);
        else { *object = nullptr; return E_NOINTERFACE; }
        AddRef();
        return S_OK;
    }
    STDMETHODIMP_(ULONG) AddRef() override { return InterlockedIncrement(&refs_); }
    STDMETHODIMP_(ULONG) Release() override
    {
        ULONG n = InterlockedDecrement(&refs_);
        if (n == 0) delete this;
        return n;
    }

    // IActivateAudioInterfaceCompletionHandler
    STDMETHODIMP ActivateCompleted(IActivateAudioInterfaceAsyncOperation *operation) override
    {
        HRESULT activate = E_FAIL;
        IUnknown *unknown = nullptr;
        HRESULT hr = operation->GetActivateResult(&activate, &unknown);
        if (SUCCEEDED(hr) && SUCCEEDED(activate) && unknown)
        {
            hr = unknown->QueryInterface(__uuidof(IAudioClient), reinterpret_cast<void **>(&client_));
            result_ = hr;
        }
        else
            result_ = FAILED(hr) ? hr : activate;
        if (unknown) unknown->Release();
        SetEvent(done_);
        return S_OK;
    }

    HANDLE done_;
    HRESULT result_;
    IAudioClient *client_;

private:
    LONG refs_;
};

static void say(const char *kind, const char *text, HRESULT hr = S_OK)
{
    if (hr != S_OK) fprintf(stderr, "%s %s (0x%08lX)\n", kind, text, static_cast<unsigned long>(hr));
    else fprintf(stderr, "%s %s\n", kind, text);
    fflush(stderr);
}

int wmain(int argc, wchar_t **argv)
{
    if (argc < 2) { say("ERROR", "usage: vs_appcapture <process id> [include|exclude]"); return 2; }
    DWORD pid = static_cast<DWORD>(_wtoi(argv[1]));
    bool include = !(argc >= 3 && _wcsicmp(argv[2], L"exclude") == 0);
    if (pid == 0) { say("ERROR", "bad process id"); return 2; }
    _setmode(_fileno(stdout), _O_BINARY);

    HRESULT hr = CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    if (FAILED(hr)) { say("ERROR", "could not start COM", hr); return 3; }

    AUDIOCLIENT_ACTIVATION_PARAMS params = {};
    params.ActivationType = AUDIOCLIENT_ACTIVATION_TYPE_PROCESS_LOOPBACK;
    params.ProcessLoopbackParams.TargetProcessId = pid;
    params.ProcessLoopbackParams.ProcessLoopbackMode =
        include ? PROCESS_LOOPBACK_MODE_INCLUDE_TARGET_PROCESS_TREE : PROCESS_LOOPBACK_MODE_EXCLUDE_TARGET_PROCESS_TREE;

    PROPVARIANT variant = {};
    variant.vt = VT_BLOB;
    variant.blob.cbSize = sizeof(params);
    variant.blob.pBlobData = reinterpret_cast<BYTE *>(&params);

    ActivateHandler *handler = new ActivateHandler();
    IActivateAudioInterfaceAsyncOperation *operation = nullptr;
    hr = ActivateAudioInterfaceAsync(VIRTUAL_AUDIO_DEVICE_PROCESS_LOOPBACK, __uuidof(IAudioClient), &variant, handler, &operation);
    if (FAILED(hr)) { say("ERROR", "this version of Windows cannot capture one program's sound", hr); return 4; }
    if (WaitForSingleObject(handler->done_, 10000) != WAIT_OBJECT_0) { say("ERROR", "Windows did not answer in time"); return 4; }
    if (FAILED(handler->result_) || handler->client_ == nullptr) { say("ERROR", "could not open that program's sound", handler->result_); return 4; }
    IAudioClient *client = handler->client_;

    WAVEFORMATEX format = {};
    format.wFormatTag = WAVE_FORMAT_PCM;
    format.nChannels = 2;
    format.nSamplesPerSec = 44100;
    format.wBitsPerSample = 16;
    format.nBlockAlign = static_cast<WORD>(format.nChannels * format.wBitsPerSample / 8);
    format.nAvgBytesPerSec = format.nSamplesPerSec * format.nBlockAlign;

    hr = client->Initialize(AUDCLNT_SHAREMODE_SHARED,
                            AUDCLNT_STREAMFLAGS_LOOPBACK | AUDCLNT_STREAMFLAGS_EVENTCALLBACK | AUDCLNT_STREAMFLAGS_NOPERSIST,
                            200000, 0, &format, nullptr);
    if (FAILED(hr)) { say("ERROR", "could not set up the capture", hr); return 5; }

    HANDLE ready = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    hr = client->SetEventHandle(ready);
    if (FAILED(hr)) { say("ERROR", "could not set up the capture event", hr); return 5; }

    IAudioCaptureClient *capture = nullptr;
    hr = client->GetService(__uuidof(IAudioCaptureClient), reinterpret_cast<void **>(&capture));
    if (FAILED(hr)) { say("ERROR", "could not read the capture", hr); return 5; }

    hr = client->Start();
    if (FAILED(hr)) { say("ERROR", "could not start the capture", hr); return 5; }
    say("OK", "capturing");

    const size_t silenceFrames = 4096;
    BYTE *silence = static_cast<BYTE *>(calloc(silenceFrames, format.nBlockAlign));
    bool running = true;
    while (running)
    {
        DWORD wait = WaitForSingleObject(ready, 250);
        if (wait != WAIT_OBJECT_0 && wait != WAIT_TIMEOUT) break;
        for (;;)
        {
            UINT32 packet = 0;
            hr = capture->GetNextPacketSize(&packet);
            if (FAILED(hr)) { say("ERROR", "the capture stopped", hr); running = false; break; }
            if (packet == 0) break;
            BYTE *data = nullptr;
            UINT32 frames = 0;
            DWORD flags = 0;
            hr = capture->GetBuffer(&data, &frames, &flags, nullptr, nullptr);
            if (FAILED(hr)) { say("ERROR", "the capture stopped", hr); running = false; break; }
            size_t want = static_cast<size_t>(frames) * format.nBlockAlign;
            bool wrote = true;
            if ((flags & AUDCLNT_BUFFERFLAGS_SILENT) || data == nullptr)
            {
                size_t left = frames;
                while (left > 0 && wrote)
                {
                    size_t part = left < silenceFrames ? left : silenceFrames;
                    wrote = fwrite(silence, format.nBlockAlign, part, stdout) == part;
                    left -= part;
                }
            }
            else
                wrote = fwrite(data, 1, want, stdout) == want;
            capture->ReleaseBuffer(frames);
            if (!wrote) { running = false; break; }          // Vision Studio closed the pipe: stop
        }
        fflush(stdout);
    }
    client->Stop();
    capture->Release();
    operation->Release();
    handler->Release();
    free(silence);
    CoUninitialize();
    return 0;
}
