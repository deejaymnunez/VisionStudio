; Inno Setup script for Vision Radio (VisionStudio).
; Build with:  ISCC.exe VisionStudio.iss   (after PyInstaller has produced dist\VisionStudio.exe)

#define MyAppName "Vision Radio"
#define MyAppVersion "2.0"
#define MyAppPublisher "Vision Records"
#define MyAppExeName "VisionStudio.exe"

[Setup]
AppId={{8D2F5B1A-3C47-4E6A-9B10-5F7A2C9E4D31}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={autopf}\{#MyAppName}
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
OutputDir=installer
OutputBaseFilename=VisionStudioSetup
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
PrivilegesRequired=lowest
PrivilegesRequiredOverridesAllowed=dialog
ArchitecturesInstallIn64BitMode=x64compatible
UninstallDisplayName={#MyAppName}
UninstallDisplayIcon={app}\{#MyAppExeName}

[Languages]
Name: "english"; MessagesFile: "compiler:Default.isl"

[Tasks]
Name: "desktopicon"; Description: "Create a &desktop shortcut"; GroupDescription: "Shortcuts:"

[Dirs]
; The playlist folder lives in the user's Documents folder (follows OneDrive if Documents was moved).
Name: "{userdocs}\VisionStudio\Playlists"

[Files]
Source: "dist\{#MyAppExeName}"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{autoprograms}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

[Registry]
; A fresh install forgets the saved folder paths and setup choices, so the setup wizard asks for them again.
; Encoder settings, shortcuts and other preferences are kept.
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: "setup_complete"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: "music_library_folder"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: ":00"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: ":15"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: ":30"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: ":45"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: "ad_break_folder"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: "rotations_json"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: "schedule_json"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: "categories_json"; Flags: deletevalue
Root: HKCU; Subkey: "Software\VisionRecords\VisionRadio"; ValueName: "playlist_output_folder"; Flags: deletevalue

[Run]
; Launches the app right after install; the first launch opens the folder setup wizard.
Filename: "{app}\{#MyAppExeName}"; Description: "Launch {#MyAppName} and run the folder setup"; Flags: nowait postinstall skipifsilent
