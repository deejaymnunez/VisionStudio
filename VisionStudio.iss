; Inno Setup script for Vision Studio (VisionStudio).
; Build with:  ISCC.exe VisionStudio.iss   (after PyInstaller has produced dist\VisionStudio.exe)

#define MyAppName "Vision Studio"
#define MyAppVersion "2.0"
#define MyAppPublisher "Vision Records"
#define MyAppExeName "VisionStudio.exe"

[Setup]
AppId={{8D2F5B1A-3C47-4E6A-9B10-5F7A2C9E4D31}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={autopf32}\{#MyAppName}
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
OutputDir=installer
OutputBaseFilename=VisionStudioSetup
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
PrivilegesRequired=admin
UsePreviousPrivileges=no
ArchitecturesInstallIn64BitMode=x64compatible
UninstallDisplayName={#MyAppName}
UninstallDisplayIcon={app}\{#MyAppExeName}

[Languages]
Name: "english"; MessagesFile: "compiler:Default.isl"

[Tasks]
Name: "desktopicon"; Description: "Create a &desktop shortcut"; GroupDescription: "Shortcuts:"

[InstallDelete]
; Remove shortcuts left by earlier builds that used the old name.
Type: files; Name: "{autoprograms}\Vision Radio.lnk"
Type: files; Name: "{autodesktop}\Vision Radio.lnk"

[Dirs]
; Playlists live inside the program folder, for example C:\Program Files (x86)\Vision Studio\Playlists,
; and every user is allowed to write to it so the app can save playlists there.
Name: "{app}\Playlists"; Permissions: users-modify
; Logs (one file per day plus errors.log) live next to Playlists, for example C:\Program Files (x86)\Vision Studio\Logs.
Name: "{app}\Logs"; Permissions: users-modify

[Files]
Source: "dist\{#MyAppExeName}"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{autoprograms}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon

; Folder paths and settings are kept across installs and updates, so nothing is cleared here.

[Run]
; Launches the app right after install. Folders are then chosen in the Settings tab.
Filename: "{app}\{#MyAppExeName}"; Description: "Launch {#MyAppName}"; Flags: nowait postinstall skipifsilent

[Code]
{ Earlier builds kept playlists in Documents\VisionStudio\Playlists. On install they are moved to the
  program folder (Playlists) and the old Documents\VisionStudio folder is removed. }
procedure MoveOldPlaylists();
var
  OldRoot, OldPlaylists, NewPlaylists, FileName: String;
  FindRec: TFindRec;
begin
  OldRoot := ExpandConstant('{userdocs}\VisionStudio');
  OldPlaylists := OldRoot + '\Playlists';
  NewPlaylists := ExpandConstant('{app}\Playlists');
  if not DirExists(OldRoot) then Exit;
  ForceDirectories(NewPlaylists);
  if DirExists(OldPlaylists) then
  begin
    if FindFirst(OldPlaylists + '\*', FindRec) then
    begin
      try
        repeat
          if (FindRec.Attributes and FILE_ATTRIBUTE_DIRECTORY) = 0 then
          begin
            FileName := FindRec.Name;
            if not FileExists(NewPlaylists + '\' + FileName) then
              FileCopy(OldPlaylists + '\' + FileName, NewPlaylists + '\' + FileName, True);
          end;
        until not FindNext(FindRec);
      finally
        FindClose(FindRec);
      end;
    end;
  end;
  DelTree(OldRoot, True, True, True);
end;

procedure CurStepChanged(CurStep: TSetupStep);
begin
  if CurStep = ssPostInstall then
    MoveOldPlaylists();
end;
