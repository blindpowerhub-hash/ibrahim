require "import"
import "android.app.*"
import "android.os.*"
import "android.widget.*"
import "android.view.*"
import "android.content.*"
import "android.content.pm.*"
import "android.net.*"
import "android.net.Uri"
import "android.net.ConnectivityManager"
import "android.util.Base64"
import "android.webkit.*"
import "java.util.ArrayList"
import "java.util.HashMap"
import "cjson"
import "android.media.MediaPlayer"
import "android.media.MediaRecorder"
import "android.media.AudioManager"
import "android.media.ToneGenerator"
import "android.bluetooth.*"
import "android.telecom.*"
import "android.speech.*"
import "android.speech.tts.*"
import "android.text.*"
import "android.hardware.*"
import "android.hardware.camera2.*"
import "android.graphics.*"
import "android.util.*"
import "android.provider.*"
import "android.database.*"
import "android.view.accessibility.*"
import "android.accessibilityservice.*"
import "android.os.Handler"
import "android.os.Looper"
import "java.io.File"
import "java.io.FileInputStream"
import "java.io.FileOutputStream"
import "java.io.*"
import "java.net.*"
import "java.net.URL"
import "java.util.*"
import "java.lang.String"
import "java.lang.Runnable"
import "java.lang.Thread"
import "java.lang.System"
import "java.lang.reflect.Array"
import "java.lang.Byte"
import "com.androlua.Http"
import "com.androlua.LuaDialog"

-- ========================================================
-- ALL OPEN SOURCE BY BLIND TECH POWER HUB
-- Developed by Ibrahim Ansari
-- ========================================================

pcall(function()
  local builder = StrictMode.VmPolicy.Builder()
  StrictMode.setVmPolicy(builder.build())
end)

local APP_TITLE = "all open source by blind Tech power hub"
local APP_DEV = "Developer: Ibrahim Ansari"
local FIREBASE_URL = "https://ibrahim-6e4a3-default-rtdb.firebaseio.com/"

local DEFAULT_VERSION = "1.32.0"
local VERSION_URL = "https://raw.githubusercontent.com/blindpowerhub-hash/ibrahim/main/virgin.txt"
local UPDATE_CODE_URL = "https://raw.githubusercontent.com/blindpowerhub-hash/ibrahim/main/main.lua"
local UPDATE_NOTE_URL = "https://raw.githubusercontent.com/blindpowerhub-hash/ibrahim/main/note.txt"

local SOUND_BASE_DIR = "/storage/emulated/0/解说/Tools/all open source by blind Tech power hub. /allopensourcebyblindTechpowerhub/"

local sp = activity.getSharedPreferences("BTP_USER_PREFS", Context.MODE_PRIVATE)
local cache_sp = activity.getSharedPreferences("BTP_OFFLINE_CACHE", Context.MODE_PRIVATE)
local update_prefs = activity.getSharedPreferences("AutoUpdatePrefs", Context.MODE_PRIVATE)
local current_username = tostring(sp.getString("username", ""))

local function getCurrentAppVersion()
  local saved_v = tostring(update_prefs.getString("installed_app_version", ""))
  if saved_v ~= "" then
    return saved_v
  end
  return DEFAULT_VERSION
end

local CURRENT_VERSION = getCurrentAppVersion()

local function resolveTargetPluginPath()
  local detected = ""
  pcall(function()
    local info = debug.getinfo(1, "S")
    if info and info.source then
      local src = tostring(info.source)
      if src:sub(1, 1) == "@" then
        detected = src:sub(2)
      elseif src:sub(1, 1) == "/" then
        detected = src
      end
    end
  end)

  if detected ~= "" and detected:sub(-4):lower() == ".lua" then
    local f = File(detected)
    if f.exists() and f.canWrite() then
      return detected
    end
  end

  local candidate_paths = {
    SOUND_BASE_DIR .. "main.lua",
    "/storage/emulated/0/解说/Tools/all open source by blind Tech power hub. /main.lua",
    "/storage/emulated/0/解说/Tools/all open source by blind Tech power hub/main.lua"
  }
  for _, cp in ipairs(candidate_paths) do
    local cf = File(cp)
    if cf.exists() then
      return cp
    end
  end

  local base_dir_file = File(SOUND_BASE_DIR)
  if base_dir_file.exists() and base_dir_file.isDirectory() then
    local files_arr = base_dir_file.listFiles()
    if files_arr ~= nil then
      local arr_len = 0
      pcall(function() arr_len = Array.getLength(files_arr) end)
      for i = 0, arr_len - 1 do
        local item_f = files_arr[i]
        if item_f ~= nil and item_f.isFile() then
          local fname = tostring(item_f.getName())
          if fname:sub(-4):lower() == ".lua" and not fname:find("temp_update", 1, true) then
            return tostring(item_f.getAbsolutePath())
          end
        end
      end
    end
  end

  local ok_dir, app_dir = pcall(function() return tostring(activity.getFilesDir().getAbsolutePath()) end)
  if ok_dir and app_dir and app_dir ~= "" then
    return app_dir .. "/main.lua"
  end
  return SOUND_BASE_DIR .. "main.lua"
end

local PLUGIN_PATH = resolveTargetPluginPath()
local updateInProgress = false
local updateDialogShowing = false
local updateDismissedThisSession = false
local isAppForeground = true

local MAX_VOICE_SECONDS = 45
local CHAT_POLL_INTERVAL_MS = 6000
local ROOM_POLL_INTERVAL_MS = 6000
local CALL_POLL_INTERVAL_MS = 2500
local CALL_RING_TIMEOUT_SEC = 35

local all_codes_data = {}
local main_content
local notif_button
local chat_tab_btn
local verified_users_map = {}
local admin_users_map = {}
local blocked_users_map = {}
local presence_handler = nil
local presence_runnable = nil

local server_is_down = false
local public_room_locked = false
local assistant_is_locked = false
local assistant_trained_items = {}

local incoming_call_handler = nil
local incoming_call_runnable = nil
local active_call_dialog = nil
local active_call_id = nil
local active_call_is_muted = false
local active_call_speaker_on = true

local bg_notif_handler = nil
local bg_notif_runnable = nil
local known_code_ids = {}
local known_notif_keys = {}
local known_bg_msg_ids = {}
local known_reaction_keys = {}
local is_first_bg_sync_done = false
local last_sound_play_time = 0
local last_seen_live_vc_id = tostring(sp.getString("last_seen_live_vc_id", ""))

local active_voice_player = nil
local active_voice_btn = nil
local active_voice_seekbar = nil
local active_voice_speed_btn = nil
local active_voice_speed = 1.0
local voice_progress_handler = Handler(Looper.getMainLooper())
local voice_progress_runnable = nil
local current_voice_playlist = {}
local current_voice_playlist_index = -1

-- ========================================================
-- OFFLINE CACHE & LOCAL STORAGE HELPERS
-- ========================================================

local function saveOfflineCache(cache_key, raw_str)
  if cache_key and raw_str and raw_str ~= "" and raw_str ~= "null" then
    pcall(function()
      cache_sp.edit().putString(tostring(cache_key), tostring(raw_str)).apply()
    end)
  end
end

local function loadOfflineCache(cache_key)
  local ok, val = pcall(function()
    return tostring(cache_sp.getString(tostring(cache_key), ""))
  end)
  if ok and val and val ~= "" then
    return val
  end
  return nil
end

-- ========================================================
-- SOUND PATHS & MEDIA / TONE HELPERS
-- ========================================================

local SOUND_NOTIF = SOUND_BASE_DIR .. "win.ogg"
local SOUND_SEND = SOUND_BASE_DIR .. "send.mp3"
local SOUND_RECEIVE = SOUND_BASE_DIR .. "receive.mp3"
local SOUND_UPLOAD = "/storage/emulated/0/Download/Digital_Scanning_Programming_Sound.mp3"
local SOUND_LIKE = SOUND_BASE_DIR .. "preview_assets_flutter_assets_assets_audio_bic_bat_hit_mp3.mp3"
local SOUND_DISCARD = SOUND_BASE_DIR .. "turn_off.ogg"
local SOUND_REACTION = SOUND_BASE_DIR .. "keyboard2type7.ogg"
local SOUND_VOICE_NEXT = SOUND_BASE_DIR .. "display_connected.mid"
local SOUND_CODE_HIT = "/storage/emulated/0/Download/btp_click.mp3"
local SOUND_SUCCESS = SOUND_BASE_DIR .. "win.ogg"

local SOUND_VOICE_PRE_SEND = SOUND_BASE_DIR .. "kv7.m4a"
local SOUND_CALL_CONNECTED = SOUND_BASE_DIR .. "ktf.m4a"
local SOUND_GROUP_CALL_RING = SOUND_BASE_DIR .. "kub.ogg"
local SOUND_CALL_VOICEMAIL_LOOP = SOUND_BASE_DIR .. "call_going_to_voicemail_-_sound_effect(128k).mp3"
local SOUND_ALERT_ANNOUNCE = SOUND_BASE_DIR .. "alert2.mp3"

local function playFallbackTone(tone_type, duration_ms)
  pcall(function()
    local tg = ToneGenerator(AudioManager.STREAM_NOTIFICATION, 85)
    tg.startTone(tone_type or ToneGenerator.TONE_PROP_BEEP, duration_ms or 220)
    local h = Handler(Looper.getMainLooper())
    h.postDelayed(Runnable({
      run = function()
        pcall(function()
          tg.stopTone()
          tg.release()
        end)
      end
    }), (duration_ms or 220) + 60)
  end)
end

local function isNetworkAvailable()
  local ok, res = pcall(function()
    local cm = activity.getSystemService(Context.CONNECTIVITY_SERVICE)
    local netInfo = cm.getActiveNetworkInfo()
    return (netInfo ~= nil and netInfo.isConnected())
  end)
  if ok then return res else return false end
end

local function playSound(path, on_done_cb, fallback_tone, looping)
  local started = false
  local mp_ref = nil
  pcall(function()
    local file = File(path)
    if file.exists() and file.length() > 0 then
      local mp = MediaPlayer()
      mp.setDataSource(path)
      if looping then
        mp.setLooping(true)
      end
      mp.prepare()
      mp.start()
      started = true
      mp_ref = mp
      if not looping then
        mp.setOnCompletionListener(MediaPlayer.OnCompletionListener{
          onCompletion = function(m)
            pcall(function() m.release() end)
            if on_done_cb then on_done_cb() end
          end
        })
      end
    end
  end)
  if not started then
    if fallback_tone then
      playFallbackTone(fallback_tone, 240)
    end
    if not looping and on_done_cb then
      on_done_cb()
    end
  end
  return mp_ref
end

local function playNotificationSoundDebounced()
  local now = os.time()
  if (now - last_sound_play_time) >= 4 then
    last_sound_play_time = now
    playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP2, false)
  end
end

local function playLimitedSound(path, duration_ms)
  local started = false
  pcall(function()
    local file = File(path)
    if file.exists() and file.length() > 0 then
      local mp = MediaPlayer()
      mp.setDataSource(path)
      mp.prepare()
      mp.start()
      started = true
      local handler = Handler(Looper.getMainLooper())
      handler.postDelayed(Runnable({
        run = function()
          pcall(function()
            if mp.isPlaying() then mp.stop() end
            mp.release()
          end)
        end
      }), duration_ms)
    end
  end)
  if not started then
    playFallbackTone(ToneGenerator.TONE_PROP_PROMPT, 220)
  end
end

local function encodeKey(s)
  return Uri.encode(tostring(s or ""))
end

local function trim(s)
  if s == nil then return "" end
  return tostring(s):match("^%s*(.-)%s*$")
end

-- ========================================================
-- CORE UI BUILDERS
-- ========================================================

function table_size(t)
  local count = 0
  if type(t) == "table" then
    for _ in pairs(t) do count = count + 1 end
  end
  return count
end

local function makeLayout(vertical, padding)
  local layout = LinearLayout(activity)
  layout.setOrientation(vertical and LinearLayout.VERTICAL or LinearLayout.HORIZONTAL)
  if padding then layout.setPadding(padding, padding, padding, padding) end
  return layout
end

local function makeText(text, size)
  local tv = TextView(activity)
  tv.setText(tostring(text or ""))
  tv.setTextSize(size or 14)
  tv.setTextColor(0xFF222222)
  return tv
end

local function makeButton(text)
  local b = Button(activity)
  b.setText(text)
  return b
end

local function showMessage(title, message)
  AlertDialog.Builder(activity)
    .setTitle(title)
    .setMessage(message)
    .setPositiveButton("OK", nil)
    .show()
end

local function showToast(message)
  Toast.makeText(activity, tostring(message), Toast.LENGTH_SHORT).show()
end

local function showOfflineCallDialog(target_label)
  local name_str = tostring(target_label or "This user")
  AlertDialog.Builder(activity)
    .setTitle("Voice Call Unavailable")
    .setMessage(name_str .. " is currently offline, voice call cannot be placed.")
    .setPositiveButton("OK", nil)
    .show()
end

-- ========================================================
-- AUTO UPDATE SYSTEM
-- ========================================================

local function getJavaByteArrayLen(byteArr)
  if byteArr == nil then return 0 end
  local ok, len = pcall(function()
    return Array.getLength(byteArr)
  end)
  if ok and type(len) == "number" then
    return len
  end
  local ok2, len2 = pcall(function()
    return #byteArr
  end)
  if ok2 and type(len2) == "number" then
    return len2
  end
  return 0
end

local function playUpdateAlertCue()
  pcall(function()
    playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_ACK, false)
    local vibrator = activity.getSystemService(Context.VIBRATOR_SERVICE)
    if vibrator then
      if Build.VERSION.SDK_INT >= 26 then
        vibrator.vibrate(VibrationEffect.createOneShot(200, VibrationEffect.DEFAULT_AMPLITUDE))
      else
        vibrator.vibrate(200)
      end
    end
  end)
end

local function showUpdateErrorDialog(title, message)
  Handler(Looper.getMainLooper()).post(Runnable({
    run = function()
      AlertDialog.Builder(activity)
        .setTitle(title)
        .setMessage(message)
        .setPositiveButton("OK", nil)
        .show()
    end
  }))
end

local function writeRawBytesSafely(target_path, rawBytes)
  local target_file = File(target_path)
  local parent_dir = target_file.getParentFile()
  if parent_dir ~= nil and not parent_dir.exists() then
    pcall(function() parent_dir.mkdirs() end)
  end

  local temp_file = File(target_path .. ".temp_update")
  local ok_temp, err_temp = pcall(function()
    local fos = FileOutputStream(temp_file, false)
    fos.write(rawBytes)
    fos.flush()
    fos.close()
  end)

  if ok_temp and temp_file.exists() and temp_file.length() > 50 then
    if target_file.exists() then
      pcall(function() target_file.delete() end)
    end
    local renamed = false
    pcall(function()
      renamed = temp_file.renameTo(target_file)
    end)
    if renamed and target_file.exists() and target_file.length() > 50 then
      return true, ""
    end
    pcall(function() temp_file.delete() end)
  else
    pcall(function() if temp_file.exists() then temp_file.delete() end end)
  end

  local ok_direct, err_direct = pcall(function()
    local fos = FileOutputStream(target_file, false)
    fos.write(rawBytes)
    fos.flush()
    fos.close()
  end)

  if ok_direct and target_file.exists() and target_file.length() > 50 then
    return true, ""
  end

  return false, tostring(err_direct or err_temp or "Storage write permission denied")
end

local function isEncryptedOrBytecodeBytes(rawBytes)
  local len = getJavaByteArrayLen(rawBytes)
  if len < 4 then return false end
  local ok, b0 = pcall(function()
    return rawBytes[0]
  end)
  if not ok or b0 == nil then
    ok, b0 = pcall(function()
      return Array.getByte(rawBytes, 0)
    end)
  end
  if ok and type(b0) == "number" then
    if b0 == 27 or b0 < 0 then
      return true
    end
  end
  return false
end

_G.BtpBinaryUpdateCallbacks = {}
local binaryUpdateCounter = 0

function onBtpBinaryUpdateDownloaded(taskId, success, onlineVersion, rawBytes)
  local cb = _G.BtpBinaryUpdateCallbacks[taskId]
  if cb then
    _G.BtpBinaryUpdateCallbacks[taskId] = nil
    cb(success, onlineVersion, rawBytes)
  end
end

local function performUpdate(onlineVersion)
  updateInProgress = true
  PLUGIN_PATH = resolveTargetPluginPath()
  binaryUpdateCounter = binaryUpdateCounter + 1
  local tId = "upd_" .. tostring(binaryUpdateCounter)
  local dlUrl = UPDATE_CODE_URL .. "?t=" .. tostring(System.currentTimeMillis())

  _G.BtpBinaryUpdateCallbacks[tId] = function(dlOk, verStr, rawBytes)
    if not dlOk or rawBytes == nil or getJavaByteArrayLen(rawBytes) <= 50 then
      updateInProgress = false
      showUpdateErrorDialog("Update Failed", "Could not download main.lua from server.")
      return
    end

    local cleanVer = trim(tostring(verStr or ""))
    local finalBytes = rawBytes

    if not isEncryptedOrBytecodeBytes(rawBytes) then
      pcall(function()
        local txt = tostring(String(rawBytes, "UTF-8"))
        if cleanVer ~= "" and txt:find("DEFAULT_VERSION", 1, true) then
          txt = txt:gsub('local%s+DEFAULT_VERSION%s*=%s*"[^"]*"', 'local DEFAULT_VERSION = "' .. cleanVer .. '"')
          txt = txt:gsub('local%s+CURRENT_VERSION%s*=%s*"[^"]*"', 'local CURRENT_VERSION = "' .. cleanVer .. '"')
          finalBytes = String(txt).getBytes("UTF-8")
        end
      end)
    end

    local written_ok, write_err = writeRawBytesSafely(PLUGIN_PATH, finalBytes)
    updateInProgress = false

    if written_ok then
      if cleanVer ~= "" then
        CURRENT_VERSION = cleanVer
        update_prefs.edit()
          .putString("installed_app_version", cleanVer)
          .putString("lastShownVersion", cleanVer)
          .apply()
      end
      updateDismissedThisSession = true

      playUpdateAlertCue()
      AlertDialog.Builder(activity)
        .setTitle("Update Successful")
        .setMessage("Successfully updated to version " .. cleanVer .. ".\n\nClick OK to restart and apply the update.")
        .setCancelable(false)
        .setPositiveButton("OK", DialogInterface.OnClickListener{
          onClick = function()
            pcall(function() stopActiveVoicePlayer(false) end)
            pcall(function() stopBackgroundNotificationWatcher() end)
            pcall(function() stopIncomingCallWatcher() end)
            pcall(function() if _G.mainDialog then _G.mainDialog.dismiss() _G.mainDialog = nil end end)
            pcall(function() if _G.mainDlg then _G.mainDlg.dismiss() _G.mainDlg = nil end end)
            pcall(function() if _G.allDialogBox then _G.allDialogBox.dismiss() _G.allDialogBox = nil end end)
            pcall(function() if _G.alertDialogBox then _G.alertDialogBox.dismiss() _G.alertDialogBox = nil end end)

            local func, err = loadfile(PLUGIN_PATH)
            if func then
              local run_ok = pcall(func)
              if not run_ok then
                showToast("Restarting app to apply update...")
                pcall(function() activity.recreate() end)
              end
            else
              showToast("Reload error: " .. tostring(err))
            end
          end
        })
        .show()
    else
      showUpdateErrorDialog(
        "Update Failed",
        "Could not save update file.\nPath: " .. tostring(PLUGIN_PATH) .. "\nReason: " .. tostring(write_err)
      )
    end
  end

  thread(function(tid, urlStr, ver)
    require "import"
    import "java.net.*"
    import "java.io.*"
    import "java.lang.reflect.Array"

    local ok, byteArr = pcall(function()
      local u = URL(urlStr)
      local conn = u.openConnection()
      conn.setRequestProperty("User-Agent", "Mozilla/5.0 (Linux; Android 10)")
      conn.setConnectTimeout(15000)
      conn.setReadTimeout(20000)
      if conn.getResponseCode() ~= 200 then
        return nil
      end
      local inp = conn.getInputStream()
      local baos = ByteArrayOutputStream()
      local buf = byte[4096]
      local n = inp.read(buf)
      while n ~= -1 do
        baos.write(buf, 0, n)
        n = inp.read(buf)
      end
      inp.close()
      baos.flush()
      local res = baos.toByteArray()
      baos.close()
      return res
    end)

    local byteLen = 0
    if ok and byteArr ~= nil then
      pcall(function()
        byteLen = Array.getLength(byteArr)
      end)
      if byteLen == 0 then
        pcall(function()
          byteLen = #byteArr
        end)
      end
    end

    local success = (ok and byteArr ~= nil and byteLen > 50)
    call("onBtpBinaryUpdateDownloaded", tid, success, ver, byteArr)
  end, tId, dlUrl, onlineVersion)
end

local function showUpdateAvailableDialogWithNote(onlineVersion, releaseNoteText)
  Handler(Looper.getMainLooper()).post(Runnable({
    run = function()
      if updateDialogShowing then return end
      updateDialogShowing = true
      playUpdateAlertCue()

      local cleanNote = trim(tostring(releaseNoteText or ""))
      local bodyMsg = "A new version (" .. onlineVersion .. ") is available.\nCurrent version: " .. CURRENT_VERSION
      if cleanNote ~= "" and cleanNote ~= "404: Not Found" then
        bodyMsg = bodyMsg .. "\n\nWhat's New:\n" .. cleanNote
      end
      bodyMsg = bodyMsg .. "\n\nWould you like to update now?"

      local dlgBuilder = AlertDialog.Builder(activity)
        .setTitle("Update Available!")
        .setMessage(bodyMsg)
        .setCancelable(false)
        .setPositiveButton("Update Now", DialogInterface.OnClickListener{
          onClick = function()
            updateDialogShowing = false
            showToast("Downloading update...")
            performUpdate(onlineVersion)
          end
        })
        .setNegativeButton("Later", DialogInterface.OnClickListener{
          onClick = function()
            updateDialogShowing = false
            updateDismissedThisSession = true
          end
        })

      if cleanNote ~= "" and cleanNote ~= "404: Not Found" then
        dlgBuilder.setNeutralButton("What's New", DialogInterface.OnClickListener{
          onClick = function()
            updateDialogShowing = false
            AlertDialog.Builder(activity)
              .setTitle("What's New in " .. onlineVersion)
              .setMessage(cleanNote)
              .setCancelable(false)
              .setPositiveButton("Update Now", DialogInterface.OnClickListener{
                onClick = function()
                  showToast("Downloading update...")
                  performUpdate(onlineVersion)
                end
              })
              .setNegativeButton("Later", DialogInterface.OnClickListener{
                onClick = function()
                  updateDismissedThisSession = true
                end
              })
              .show()
          end
        })
      end

      dlgBuilder.show()
    end
  }))
end

function checkUpdate(manualCheck)
  if updateInProgress or updateDialogShowing then
    if manualCheck then showToast("Update already in progress...") end
    return
  end

  if (not manualCheck) and updateDismissedThisSession then
    return
  end

  if not isNetworkAvailable() then
    if manualCheck then
      showUpdateErrorDialog("No Internet", "Please connect to the internet and try again.")
    end
    return
  end

  if manualCheck then
    showToast("Checking for updates...")
  end

  CURRENT_VERSION = getCurrentAppVersion()
  local timestamp = tostring(System.currentTimeMillis())

  Http.get(VERSION_URL .. "?t=" .. timestamp, nil, "utf-8", nil, function(code, response)
    if code == 200 and response then
      local onlineVersion = trim(response)
      local alreadyInstalled = tostring(update_prefs.getString("installed_app_version", ""))

      if onlineVersion ~= "" and onlineVersion ~= CURRENT_VERSION and onlineVersion ~= alreadyInstalled then
        Http.get(UPDATE_NOTE_URL .. "?t=" .. timestamp, nil, "utf-8", nil, function(noteCode, noteResp)
          local noteStr = ""
          if noteCode == 200 and noteResp then
            noteStr = trim(tostring(noteResp))
          end
          showUpdateAvailableDialogWithNote(onlineVersion, noteStr)
        end)
      else
        if onlineVersion ~= "" then
          CURRENT_VERSION = onlineVersion
          update_prefs.edit().putString("installed_app_version", onlineVersion).apply()
        end
        if manualCheck then
          showMessage("Up to Date", "You are already using the latest version (" .. CURRENT_VERSION .. ").")
        end
      end
    elseif manualCheck then
      showUpdateErrorDialog("Update Check Failed", "Unable to reach version server (HTTP " .. tostring(code) .. ").")
    end
  end)
end

-- ========================================================
-- SERVER STATUS & ROLE HELPERS
-- ========================================================

local function isDeveloper(name)
  local n = trim(tostring(name or "")):lower()
  return (n:find("ibrahim", 1, true) ~= nil)
end

local function isVerifiedUser(name)
  if isDeveloper(name) then return true end
  local n = trim(tostring(name or "")):lower()
  if n == "" then return false end
  for k, v in pairs(verified_users_map) do
    if trim(Uri.decode(tostring(k))):lower() == n and (v == true or v == "true") then
      return true
    end
  end
  return false
end

local function isAdminUser(name)
  local n = trim(tostring(name or "")):lower()
  if n == "" then return false end
  for k, v in pairs(admin_users_map) do
    if trim(Uri.decode(tostring(k))):lower() == n and (v == true or v == "true") then
      return true
    end
  end
  return false
end

local function canBypassRoomLock(name)
  return isDeveloper(name) or isVerifiedUser(name) or isAdminUser(name)
end

local function getRoleBadgeText(name)
  name = tostring(name or "")
  if isVerifiedUser(name) then
    return name .. " Verified"
  elseif isAdminUser(name) then
    return name .. " Admin"
  end
  return name
end

local function notifyServerDownIfNeeded()
  if server_is_down and not isDeveloper(current_username) then
    showToast("This message is not sent. Server is currently down. Please try again later.")
    return true
  end
  return false
end

-- ========================================================
-- SEEN BY COUNTER & PLAYED STATUS HELPERS
-- ========================================================

local function formatSeenByText(seen_by_tbl)
  local cnt = 0
  if type(seen_by_tbl) == "table" then
    for k, v in pairs(seen_by_tbl) do
      if v == true or v == "true" or type(v) == "string" then
        cnt = cnt + 1
      end
    end
  end
  if cnt <= 0 then return "" end
  if cnt == 1 then
    return "Seen by 1 user"
  end
  return "Seen by " .. tostring(cnt) .. " users"
end

local function isVoicePlayedByMe(msg_tbl)
  if type(msg_tbl) ~= "table" or type(msg_tbl.played_by) ~= "table" then return false end
  local my_norm = trim(current_username):lower()
  for k, v in pairs(msg_tbl.played_by) do
    local un = type(v) == "string" and v or Uri.decode(tostring(k))
    if trim(tostring(un)):lower() == my_norm then
      return true
    end
  end
  return false
end

local function markMessageSeenInFirebase(firebase_msg_base_url)
  if current_username == "" or not isNetworkAvailable() then return end
  http_post_or_put(firebase_msg_base_url .. "/seen_by/" .. encodeKey(current_username) .. ".json", "PUT", true, function() end)
end

local function markVoicePlayedInFirebase(firebase_msg_base_url, played_tv)
  if current_username == "" then return end
  if played_tv then
    pcall(function() played_tv.setText("Played") end)
  end
  if isNetworkAvailable() then
    http_post_or_put(firebase_msg_base_url .. "/played_by/" .. encodeKey(current_username) .. ".json", "PUT", true, function() end)
  end
end

-- ========================================================
-- HIGH-CLARITY AUDIO RECORDER & CACHED VOICE PLAYER
-- ========================================================

local function startHighClarityRecording(out_path)
  local rec_aac = MediaRecorder()
  local ok_aac = pcall(function()
    rec_aac.setAudioSource(MediaRecorder.AudioSource.VOICE_RECOGNITION)
    rec_aac.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4)
    rec_aac.setAudioEncoder(MediaRecorder.AudioEncoder.AAC)
    rec_aac.setAudioSamplingRate(32000)
    rec_aac.setAudioEncodingBitRate(64000)
    rec_aac.setOutputFile(out_path)
    rec_aac.prepare()
    rec_aac.start()
  end)
  if ok_aac then return rec_aac end
  pcall(function() rec_aac.release() end)

  local rec_wb = MediaRecorder()
  local ok_wb = pcall(function()
    rec_wb.setAudioSource(MediaRecorder.AudioSource.MIC)
    rec_wb.setOutputFormat(MediaRecorder.OutputFormat.THREE_GPP)
    rec_wb.setAudioEncoder(MediaRecorder.AudioEncoder.AMR_WB)
    rec_wb.setAudioSamplingRate(16000)
    rec_wb.setAudioEncodingBitRate(23850)
    rec_wb.setOutputFile(out_path)
    rec_wb.prepare()
    rec_wb.start()
  end)
  if ok_wb then return rec_wb end
  pcall(function() rec_wb.release() end)

  local rec_nb = MediaRecorder()
  local ok_nb = pcall(function()
    rec_nb.setAudioSource(MediaRecorder.AudioSource.MIC)
    rec_nb.setOutputFormat(MediaRecorder.OutputFormat.THREE_GPP)
    rec_nb.setAudioEncoder(MediaRecorder.AudioEncoder.AMR_NB)
    rec_nb.setAudioSamplingRate(8000)
    rec_nb.setAudioEncodingBitRate(12200)
    rec_nb.setOutputFile(out_path)
    rec_nb.prepare()
    rec_nb.start()
  end)
  if ok_nb then return rec_nb end

  pcall(function() rec_nb.release() end)
  return nil
end

local function encodeFileToBase64(filepath)
  local ok, result = pcall(function()
    local file = File(filepath)
    if not file.exists() then return nil end
    local len = file.length()
    if len <= 0 or len > 750000 then return nil end
    local fis = FileInputStream(file)
    local byte_arr = Array.newInstance(Byte.TYPE, len)
    local offset = 0
    while offset < len do
      local read_count = fis.read(byte_arr, offset, len - offset)
      if read_count < 0 then break end
      offset = offset + read_count
    end
    fis.close()
    return Base64.encodeToString(byte_arr, Base64.NO_WRAP)
  end)
  if ok then return result else return nil end
end

local function decodeBase64ToFile(b64_str, out_filepath)
  local ok, res = pcall(function()
    local existing = File(out_filepath)
    if existing.exists() and existing.length() > 0 then
      return true
    end
    if not b64_str or b64_str == "" then return false end
    local decoded_bytes = Base64.decode(tostring(b64_str), Base64.DEFAULT)
    local fos = FileOutputStream(out_filepath)
    fos.write(decoded_bytes)
    fos.flush()
    fos.close()
    return true
  end)
  if ok then return res else return false end
end

local function applyPlayerSpeed(mp, speed_val)
  pcall(function()
    if Build.VERSION.SDK_INT >= 23 and mp ~= nil then
      local params = mp.getPlaybackParams()
      params.setSpeed(speed_val)
      mp.setPlaybackParams(params)
    end
  end)
end

function stopActiveVoicePlayer(keep_queue)
  if voice_progress_runnable ~= nil then
    pcall(function() voice_progress_handler.removeCallbacks(voice_progress_runnable) end)
    voice_progress_runnable = nil
  end
  if active_voice_player ~= nil then
    pcall(function()
      if active_voice_player.isPlaying() then
        active_voice_player.stop()
      end
      active_voice_player.release()
    end)
    active_voice_player = nil
  end
  if active_voice_btn ~= nil then
    pcall(function()
      local orig = active_voice_btn.getTag()
      if orig then active_voice_btn.setText(tostring(orig)) end
    end)
    active_voice_btn = nil
  end
  if active_voice_seekbar ~= nil then
    pcall(function()
      active_voice_seekbar.setProgress(0)
    end)
    active_voice_seekbar = nil
  end
  active_voice_speed_btn = nil
  if not keep_queue then
    current_voice_playlist_index = -1
  end
end

local function playVoiceQueueAtIndex(idx)
  local entry = current_voice_playlist[idx]
  if not entry then
    stopActiveVoicePlayer(false)
    return
  end

  stopActiveVoicePlayer(true)
  current_voice_playlist_index = idx

  local safe_id = tostring(entry.msg_id or "msg"):gsub("[^%w_]", "_")
  local temp_play_path = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_play_" .. safe_id .. ".m4a"
  local decoded_ok = decodeBase64ToFile(entry.audio_b64, temp_play_path)
  if not decoded_ok then
    showToast("Unable to play voice message.")
    current_voice_playlist_index = -1
    return
  end

  local started_ok = pcall(function()
    local mp = MediaPlayer()
    mp.setDataSource(temp_play_path)
    mp.prepare()
    applyPlayerSpeed(mp, active_voice_speed)
    mp.start()

    active_voice_player = mp
    active_voice_btn = entry.play_btn
    active_voice_seekbar = entry.seek_bar
    active_voice_speed_btn = entry.speed_btn

    if entry.firebase_msg_url then
      markVoicePlayedInFirebase(entry.firebase_msg_url, entry.played_tv)
    end

    entry.play_btn.setText("Stop (" .. entry.dur_str .. ")")
    if active_voice_speed == 1.5 then entry.speed_btn.setText("1.5x")
    elseif active_voice_speed == 2.0 then entry.speed_btn.setText("2x")
    else entry.speed_btn.setText("1x") end

    voice_progress_runnable = Runnable({
      run = function()
        if active_voice_player ~= nil and active_voice_btn == entry.play_btn then
          pcall(function()
            if active_voice_player.isPlaying() then
              local cur = active_voice_player.getCurrentPosition()
              local tot = active_voice_player.getDuration()
              if tot > 0 then
                local pct = math.floor((cur / tot) * 100)
                if pct > 100 then pct = 100 end
                entry.seek_bar.setProgress(pct)
              end
              voice_progress_handler.postDelayed(voice_progress_runnable, 250)
            end
          end)
        end
      end
    })
    voice_progress_handler.postDelayed(voice_progress_runnable, 250)

    mp.setOnCompletionListener(MediaPlayer.OnCompletionListener{
      onCompletion = function()
        local next_idx = idx + 1
        stopActiveVoicePlayer(true)
        if current_voice_playlist[next_idx] ~= nil then
          playSound(SOUND_VOICE_NEXT, function()
            if current_voice_playlist[next_idx] ~= nil then
              playVoiceQueueAtIndex(next_idx)
            end
          end, ToneGenerator.TONE_PROP_BEEP, false)
        else
          current_voice_playlist_index = -1
        end
      end
    })
  end)

  if not started_ok then
    stopActiveVoicePlayer(false)
    showToast("Error playing voice message.")
  end
end

local function buildVoiceBubblePlayer(parent_bubble, msg_tbl, dur_str, playlist_ref, firebase_msg_url)
  local msg_id = msg_tbl.id
  local audio_b64 = msg_tbl.audio_base64
  local controls_row = makeLayout(false, 2)

  local play_label = "Play (" .. dur_str .. ")"
  local play_btn = makeButton(play_label)
  play_btn.setTag(play_label)

  local speed_btn = makeButton("1x")

  controls_row.addView(play_btn, LinearLayout.LayoutParams(0, -2, 1))
  controls_row.addView(speed_btn, LinearLayout.LayoutParams(-2, -2))
  parent_bubble.addView(controls_row, LinearLayout.LayoutParams(-1, -2))

  local seek_bar = SeekBar(activity)
  seek_bar.setMax(100)
  seek_bar.setProgress(0)
  seek_bar.setContentDescription("Voice message slider, 0 percent")
  parent_bubble.addView(seek_bar, LinearLayout.LayoutParams(-1, -2))

  local is_me = (trim(tostring(msg_tbl.sender or "")):lower() == trim(current_username):lower())
  local played_label_txt = isVoicePlayedByMe(msg_tbl) and "Played" or "Not played"
  if is_me then
    local any_played = (type(msg_tbl.played_by) == "table" and table_size(msg_tbl.played_by) > 0)
    played_label_txt = any_played and "Played" or "Not played"
  end

  local played_tv = makeText(played_label_txt, 11)
  played_tv.setTextColor(0xFF455A64)
  played_tv.setPadding(0, 2, 0, 2)
  parent_bubble.addView(played_tv)

  local my_playlist_idx = 1
  if type(playlist_ref) == "table" then
    table.insert(playlist_ref, {
      msg_id = msg_id,
      audio_b64 = audio_b64,
      dur_str = dur_str,
      play_btn = play_btn,
      seek_bar = seek_bar,
      speed_btn = speed_btn,
      played_tv = played_tv,
      firebase_msg_url = firebase_msg_url
    })
    my_playlist_idx = #playlist_ref
  end

  speed_btn.setOnClickListener(function()
    if active_voice_speed == 1.0 then
      active_voice_speed = 1.5
      speed_btn.setText("1.5x")
    elseif active_voice_speed == 1.5 then
      active_voice_speed = 2.0
      speed_btn.setText("2x")
    else
      active_voice_speed = 1.0
      speed_btn.setText("1x")
    end
    if active_voice_btn == play_btn and active_voice_player ~= nil then
      applyPlayerSpeed(active_voice_player, active_voice_speed)
    end
  end)

  seek_bar.setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener{
    onProgressChanged = function(sb, progress, from_user)
      sb.setContentDescription("Voice message slider, " .. tostring(progress) .. " percent")
      if from_user and active_voice_btn == play_btn and active_voice_player ~= nil then
        pcall(function()
          local total_dur = active_voice_player.getDuration()
          if total_dur > 0 then
            local seek_ms = math.floor((progress / 100) * total_dur)
            active_voice_player.seekTo(seek_ms)
          end
        end)
      end
    end,
    onStartTrackingTouch = function(sb) end,
    onStopTrackingTouch = function(sb) end
  })

  play_btn.setOnClickListener(function()
    if active_voice_btn == play_btn then
      stopActiveVoicePlayer(false)
      return
    end
    if type(playlist_ref) == "table" then
      current_voice_playlist = playlist_ref
      playVoiceQueueAtIndex(my_playlist_idx)
    else
      current_voice_playlist = {{
        msg_id = msg_id,
        audio_b64 = audio_b64,
        dur_str = dur_str,
        play_btn = play_btn,
        seek_bar = seek_bar,
        speed_btn = speed_btn,
        played_tv = played_tv,
        firebase_msg_url = firebase_msg_url
      }}
      playVoiceQueueAtIndex(1)
    end
  end)
end

-- ========================================================
-- REACTION VIEWER & TALKBACK-ACCESSIBLE DAY LABELS
-- ========================================================

local function renderClickableReactions(parent_bubble, reactions_tbl)
  if type(reactions_tbl) ~= "table" or table_size(reactions_tbl) == 0 then return end
  local summary_list = {}
  local detail_lines = {}
  for ruser_key, rval in pairs(reactions_tbl) do
    local dec_u = Uri.decode(tostring(ruser_key))
    table.insert(summary_list, tostring(rval))
    table.insert(detail_lines, dec_u .. ": " .. tostring(rval))
  end

  local rx_tv = makeText("Reactions (" .. tostring(#detail_lines) .. "): " .. table.concat(summary_list, ", ") .. " (Tap to view)", 12)
  rx_tv.setTextColor(0xFF1E88E5)
  rx_tv.setPadding(0, 4, 0, 2)
  rx_tv.setFocusable(true)
  rx_tv.setClickable(true)
  rx_tv.setContentDescription("Reactions: " .. table.concat(detail_lines, ", ") .. ". Double tap to see details.")
  parent_bubble.addView(rx_tv)

  rx_tv.setOnClickListener(function()
    AlertDialog.Builder(activity)
      .setTitle("Message Reactions (" .. tostring(#detail_lines) .. ")")
      .setMessage(table.concat(detail_lines, "\n"))
      .setPositiveButton("Close", nil)
      .show()
  end)
end

local function createAccessibleDayHeader(day_lbl)
  local day_tv = makeText(day_lbl, 13)
  day_tv.setTextColor(0xFF37474F)
  day_tv.setBackgroundColor(0xFFE0E0E0)
  day_tv.setGravity(Gravity.CENTER)
  day_tv.setPadding(12, 8, 12, 8)
  day_tv.setFocusable(true)
  day_tv.setContentDescription(day_lbl)
  return day_tv
end

-- ========================================================
-- SEEN NOTIFICATIONS & LOCAL HIDDEN GROUPS STORAGE
-- ========================================================

local function getSeenNotifsMap()
  local raw = tostring(sp.getString("seen_notif_ids_json", "{}"))
  local ok, tbl = pcall(cjson.decode, raw)
  if ok and type(tbl) == "table" then return tbl end
  return {}
end

local function saveSeenNotifsMap(tbl)
  local ok, raw = pcall(cjson.encode, tbl)
  if ok and raw then
    sp.edit().putString("seen_notif_ids_json", raw).apply()
  end
end

local function getLocalHiddenMap(pref_key)
  local raw = tostring(sp.getString(pref_key, "{}"))
  local ok, tbl = pcall(cjson.decode, raw)
  if ok and type(tbl) == "table" then return tbl end
  return {}
end

local function saveLocalHiddenMap(pref_key, tbl)
  local ok, raw = pcall(cjson.encode, tbl)
  if ok and raw then
    sp.edit().putString(pref_key, raw).apply()
  end
end

-- ========================================================
-- ROLES, SERVER SETTINGS & DATE FORMATTING
-- ========================================================

local function loadVerifiedUsers(callback)
  if not isNetworkAvailable() then
    local cached = loadOfflineCache("verified_users")
    if cached then
      local ok, data = pcall(cjson.decode, cached)
      if ok and type(data) == "table" then verified_users_map = data end
    end
    if callback then callback() end
    return
  end
  Http.get(FIREBASE_URL .. "verified_users.json", nil, "utf-8", nil, function(code, content)
    verified_users_map = {}
    if code == 200 and content and content ~= "null" then
      saveOfflineCache("verified_users", content)
      local ok, data = pcall(cjson.decode, content)
      if ok and type(data) == "table" then
        verified_users_map = data
      end
    end
    if callback then callback() end
  end)
end

local function loadAdminUsers(callback)
  if not isNetworkAvailable() then
    local cached = loadOfflineCache("admin_users")
    if cached then
      local ok, data = pcall(cjson.decode, cached)
      if ok and type(data) == "table" then admin_users_map = data end
    end
    if callback then callback() end
    return
  end
  Http.get(FIREBASE_URL .. "admin_users.json", nil, "utf-8", nil, function(code, content)
    admin_users_map = {}
    if code == 200 and content and content ~= "null" then
      saveOfflineCache("admin_users", content)
      local ok, data = pcall(cjson.decode, content)
      if ok and type(data) == "table" then
        admin_users_map = data
      end
    end
    if callback then callback() end
  end)
end

local function loadBlockedUsers(callback)
  if not isNetworkAvailable() then
    if callback then callback() end
    return
  end
  Http.get(FIREBASE_URL .. "blocked.json", nil, "utf-8", nil, function(code, content)
    blocked_users_map = {}
    if code == 200 and content and content ~= "null" then
      local ok, data = pcall(cjson.decode, content)
      if ok and type(data) == "table" then
        blocked_users_map = data
      end
    end
    if callback then callback() end
  end)
end

local function syncServerAndRoomSettings(callback)
  if not isNetworkAvailable() then
    local cached = loadOfflineCache("server_settings")
    if cached then
      local ok, sdata = pcall(cjson.decode, cached)
      if ok and type(sdata) == "table" then
        server_is_down = (sdata.server_down == true or sdata.server_down == "true")
        public_room_locked = (sdata.public_room_locked == true or sdata.public_room_locked == "true")
        assistant_is_locked = (sdata.assistant_locked == true or sdata.assistant_locked == "true")
      end
    end
    if callback then callback() end
    return
  end
  Http.get(FIREBASE_URL .. "settings.json", nil, "utf-8", nil, function(code, content)
    if code == 200 and content and content ~= "null" then
      saveOfflineCache("server_settings", content)
      local ok, sdata = pcall(cjson.decode, content)
      if ok and type(sdata) == "table" then
        server_is_down = (sdata.server_down == true or sdata.server_down == "true")
        public_room_locked = (sdata.public_room_locked == true or sdata.public_room_locked == "true")
        assistant_is_locked = (sdata.assistant_locked == true or sdata.assistant_locked == "true")
        assistant_trained_items = {}
        if type(sdata.assistant_training) == "table" then
          for _, item in pairs(sdata.assistant_training) do
            if type(item) == "table" and trim(tostring(item.q or "")) ~= "" and trim(tostring(item.a or "")) ~= "" then
              table.insert(assistant_trained_items, item)
            end
          end
        end
      end
    end
    if callback then callback() end
  end)
end

local function getVerifiedName(name)
  return getRoleBadgeText(name)
end

local function getDayLabelFromRaw(timestamp_raw)
  local s = tostring(timestamp_raw or "")
  if #s < 8 then return "" end
  local msg_ymd = s:sub(1, 8)
  local today_ymd = os.date("%Y%m%d")
  local yesterday_ymd = os.date("%Y%m%d", os.time() - 86400)
  if msg_ymd == today_ymd then
    return "Today"
  elseif msg_ymd == yesterday_ymd then
    return "Yesterday"
  else
    local y = s:sub(1, 4)
    local m = tonumber(s:sub(5, 6)) or 1
    local d = tonumber(s:sub(7, 8)) or 1
    local months = {"Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"}
    return string.format("%02d %s %s", d, months[m] or "Jan", y)
  end
end

-- ========================================================
-- FIREBASE HTTP HELPERS
-- ========================================================

function http_get(url, callback)
  if not isNetworkAvailable() then
    if callback then callback(false, nil) end
    return
  end
  Http.get(url, nil, "utf-8", nil, function(code, content)
    if code == 200 then
      callback(true, content)
    else
      callback(false, content)
    end
  end)
end

function http_post_or_put(url, method, data_table, callback)
  if not isNetworkAvailable() then
    if callback then callback(false, nil) end
    return
  end
  local ok, json_str
  if type(data_table) == "string" then
    json_str = cjson.encode(data_table)
    ok = true
  elseif type(data_table) == "boolean" or type(data_table) == "number" then
    json_str = tostring(data_table)
    ok = true
  else
    ok, json_str = pcall(cjson.encode, data_table)
  end

  if not ok then
    if callback then callback(false, nil) end
    return
  end

  local function finish(code, content)
    if callback then callback(code == 200 or code == 201, content) end
  end

  if method == "PUT" and Http.put then
    Http.put(url, json_str, "utf-8", nil, finish)
  else
    Http.post(url, json_str, "utf-8", nil, finish)
  end
end

function http_delete(url, callback)
  if not isNetworkAvailable() then
    if callback then callback(false, nil) end
    return
  end
  Http.delete(url, nil, "utf-8", nil, function(code, content)
    if callback then callback(code == 200, content) end
  end)
end

local function registerUserToFirebase(username)
  if not username or username == "" or not isNetworkAvailable() then return end
  local user_data = {
    username = username,
    last_active = os.date("%I:%M %p, %d %b"),
    last_active_epoch = os.time()
  }
  http_post_or_put(FIREBASE_URL .. "registered_users/" .. encodeKey(username) .. ".json", "PUT", user_data, function() end)
end

local function updatePresence(status_str)
  if current_username == "" or not isNetworkAvailable() then return end
  local share_presence = sp.getBoolean("share_presence_enabled", true)
  if not share_presence then return end

  local presence_data = {
    username = current_username,
    status = status_str or "online",
    last_seen = os.date("%I:%M %p, %d %b"),
    time_epoch = os.time()
  }
  http_post_or_put(FIREBASE_URL .. "user_presence/" .. encodeKey(current_username) .. ".json", "PUT", presence_data, function() end)
end

local function stopPresenceTracking()
  if presence_handler and presence_runnable then
    pcall(function() presence_handler.removeCallbacks(presence_runnable) end)
  end
  presence_handler = nil
  presence_runnable = nil
end

local function startPresenceTracking()
  if not isAppForeground then return end
  updatePresence("online")
  if presence_handler == nil then
    presence_handler = Handler(Looper.getMainLooper())
    presence_runnable = Runnable({
      run = function()
        if isAppForeground then
          updatePresence("online")
          presence_handler.postDelayed(presence_runnable, 180000)
        else
          stopPresenceTracking()
        end
      end
    })
    presence_handler.postDelayed(presence_runnable, 180000)
  end
end

local function getOnlineUsersSummary(presence_json_str)
  if not isNetworkAvailable() then
    return 0, "", {}
  end
  local online_names = {}
  if presence_json_str and presence_json_str ~= "null" then
    local ok_p, pdata = pcall(cjson.decode, presence_json_str)
    if ok_p and type(pdata) == "table" then
      local now = os.time()
      local seen_norm = {}
      for pk, p in pairs(pdata) do
        if type(p) == "table" and p.status == "online" and (now - tonumber(p.time_epoch or 0) < 240) then
          local uname = trim(tostring(p.username or Uri.decode(tostring(pk))))
          if uname ~= "" then
            local low = uname:lower()
            if not seen_norm[low] then
              seen_norm[low] = true
              table.insert(online_names, uname)
            end
          end
        end
      end
    end
  end

  if current_username ~= "" and isNetworkAvailable() then
    local my_low = trim(current_username):lower()
    local has_me = false
    for _, n in ipairs(online_names) do
      if trim(n):lower() == my_low then has_me = true break end
    end
    if not has_me then
      table.insert(online_names, 1, current_username)
    end
  end

  local cnt = #online_names
  local names_str = table.concat(online_names, ", ")
  return cnt, names_str, online_names
end

-- ========================================================
-- REAL-TIME LIVE MICROPHONE VOICE CALL ENGINE (WEBVIEW WEBRTC)
-- ========================================================

local function setCallAudioMode(speaker_on, muted)
  pcall(function()
    local am = activity.getSystemService(Context.AUDIO_SERVICE)
    am.setMode(AudioManager.MODE_IN_COMMUNICATION)
    am.setSpeakerphoneOn(speaker_on and true or false)
    am.setMicrophoneMute(muted and true or false)
  end)
end

local function resetCallAudioMode()
  pcall(function()
    local am = activity.getSystemService(Context.AUDIO_SERVICE)
    am.setMicrophoneMute(false)
    am.setSpeakerphoneOn(false)
    am.setMode(AudioManager.MODE_NORMAL)
  end)
end

local function isUserCurrentlyOnline(target_name, callback)
  if not isNetworkAvailable() then
    if callback then callback(false) end
    return
  end
  http_get(FIREBASE_URL .. "user_presence/" .. encodeKey(target_name) .. ".json", function(s, r)
    if s and r and r ~= "null" then
      local ok, data = pcall(cjson.decode, r)
      if ok and type(data) == "table" then
        local now = os.time()
        local last_t = tonumber(data.time_epoch or 0)
        if data.status == "online" and (now - last_t < 240) then
          if callback then callback(true) end
          return
        end
      end
    end
    if callback then callback(false) end
  end)
end

local function buildLiveWebRtcCallHtml(call_id, my_user, fb_base)
  local safe_cid = tostring(call_id):gsub("[^%w_]", "_")
  local safe_me = tostring(my_user):gsub("[^%w_]", "_")
  return [[
<!DOCTYPE html>
<html>
<head><meta name="viewport" content="width=device-width,initial-scale=1"></head>
<body style="font-family:sans-serif;background:#E8F5E9;color:#1B5E20;padding:8px;margin:0;border-radius:6px;">
<div id="rtcStatus" style="font-size:13px;font-weight:bold;">Initializing Live Real-Time Microphone...</div>
<div id="remoteAudios"></div>
<script>
const CALL_ID = "]] .. safe_cid .. [[";
const MY_ID = "]] .. safe_me .. [[";
const FB_URL = "]] .. fb_base .. [[voice_calls/" + CALL_ID + "/webrtc_signals";
let localStream = null;
let isMuted = false;
let peers = {};
let seenSignals = {};
let pollTimer = null;

function setStatus(txt) {
  const el = document.getElementById("rtcStatus");
  if (el) el.innerText = txt;
}

window.setMicMuteState = function(m) {
  isMuted = !!m;
  if (localStream) {
    localStream.getAudioTracks().forEach(t => { t.enabled = !isMuted; });
  }
  setStatus(isMuted ? "Live Mic: Muted" : "Live Mic: Active (Real-Time Audio)");
};

window.stopLiveWebRtc = function() {
  if (pollTimer) clearInterval(pollTimer);
  Object.values(peers).forEach(pc => { try { pc.close(); } catch(e){} });
  peers = {};
  if (localStream) {
    localStream.getTracks().forEach(t => { try { t.stop(); } catch(e){} });
    localStream = null;
  }
};

function sendSignal(toUser, payload) {
  fetch(FB_URL + "/" + encodeURIComponent(toUser) + ".json", {
    method: "POST",
    body: JSON.stringify(Object.assign({ from: MY_ID, ts: Date.now() }, payload))
  }).catch(()=>{});
}

function createPeer(remoteUser, isInitiator) {
  if (peers[remoteUser]) return peers[remoteUser];
  const pc = new RTCPeerConnection({
    iceServers: [
      { urls: "stun:stun.l.google.com:19302" },
      { urls: "stun:stun1.l.google.com:19302" }
    ]
  });
  peers[remoteUser] = pc;

  if (localStream) {
    localStream.getTracks().forEach(track => pc.addTrack(track, localStream));
  }

  pc.onicecandidate = (e) => {
    if (e.candidate) {
      sendSignal(remoteUser, { type: "candidate", candidate: e.candidate });
    }
  };

  pc.ontrack = (e) => {
    let aud = document.getElementById("aud_" + remoteUser);
    if (!aud) {
      aud = document.createElement("audio");
      aud.id = "aud_" + remoteUser;
      aud.autoplay = true;
      aud.playsInline = true;
      document.getElementById("remoteAudios").appendChild(aud);
    }
    aud.srcObject = e.streams[0];
    aud.play().catch(()=>{});
    setStatus("Live Voice Connected (Real-Time Audio Active)");
  };

  if (isInitiator) {
    pc.createOffer().then(offer => pc.setLocalDescription(offer)).then(() => {
      sendSignal(remoteUser, { type: "offer", sdp: pc.localDescription });
    }).catch(()=>{});
  }
  return pc;
}

async function pollSignals() {
  try {
    const res = await fetch(FB_URL + "/" + encodeURIComponent(MY_ID) + ".json");
    const data = await res.json();
    if (!data) return;
    for (const [k, sig] of Object.entries(data)) {
      if (seenSignals[k] || !sig || !sig.from || sig.from === MY_ID) continue;
      seenSignals[k] = true;
      fetch(FB_URL + "/" + encodeURIComponent(MY_ID) + "/" + k + ".json", { method: "DELETE" }).catch(()=>{});

      if (sig.type === "join") {
        createPeer(sig.from, true);
      } else if (sig.type === "offer") {
        const pc = createPeer(sig.from, false);
        await pc.setRemoteDescription(new RTCSessionDescription(sig.sdp));
        const ans = await pc.createAnswer();
        await pc.setLocalDescription(ans);
        sendSignal(sig.from, { type: "answer", sdp: pc.localDescription });
      } else if (sig.type === "answer") {
        const pc = peers[sig.from];
        if (pc) await pc.setRemoteDescription(new RTCSessionDescription(sig.sdp));
      } else if (sig.type === "candidate") {
        const pc = peers[sig.from];
        if (pc && sig.candidate) await pc.addIceCandidate(new RTCIceCandidate(sig.candidate));
      }
    }
  } catch (err) {}
}

(async function start() {
  try {
    localStream = await navigator.mediaDevices.getUserMedia({
      audio: { echoCancellation: true, noiseSuppression: true, autoGainControl: true },
      video: false
    });
    setStatus("Live Mic: Active (Real-Time Audio)");
    const pRes = await fetch("]] .. fb_base .. [[voice_calls/" + CALL_ID + "/participants.json");
    const parts = await pRes.json();
    if (parts) {
      Object.values(parts).forEach(pName => {
        const cleanP = String(pName).replace(/[^a-zA-Z0-9_]/g, "_");
        if (cleanP && cleanP !== MY_ID) {
          sendSignal(cleanP, { type: "join" });
        }
      });
    }
    pollTimer = setInterval(pollSignals, 1500);
  } catch (e) {
    setStatus("Live Mic Ready (Grant Microphone Permission if prompted)");
  }
})();
</script>
</body>
</html>
]]
end

function openActiveCallSessionDialog(call_id, initial_call_data, start_dial_loop)
  if active_call_dialog ~= nil then return end
  active_call_id = call_id
  active_call_is_muted = false
  active_call_speaker_on = true
  setCallAudioMode(true, false)

  local layout = makeLayout(true, 16)
  local call_type = tostring(initial_call_data.call_type or "direct")
  local call_label = tostring(initial_call_data.title or initial_call_data.target or "Voice Call")

  local status_tv = makeText("Connecting real-time voice call with " .. call_label .. "...", 15)
  status_tv.setTextColor(0xFF0D47A1)
  layout.addView(status_tv)

  local participants_tv = makeText("Participants: Loading...", 13)
  participants_tv.setPadding(0, 6, 0, 8)
  layout.addView(participants_tv)

  local rtc_webview = WebView(activity)
  pcall(function()
    local ws = rtc_webview.getSettings()
    ws.setJavaScriptEnabled(true)
    ws.setDomStorageEnabled(true)
    ws.setMediaPlaybackRequiresUserGesture(false)
    rtc_webview.setWebChromeClient(WebChromeClient{
      onPermissionRequest = function(req)
        pcall(function() req.grant(req.getResources()) end)
      end
    })
    local html_code = buildLiveWebRtcCallHtml(call_id, current_username, FIREBASE_URL)
    rtc_webview.loadDataWithBaseURL("https://blindtechpowerhub.local/", html_code, "text/html", "UTF-8", nil)
  end)
  layout.addView(rtc_webview, LinearLayout.LayoutParams(-1, 80))

  local ctrl_row_1 = makeLayout(false, 4)
  local mute_btn = makeButton("Mute Microphone")
  mute_btn.setContentDescription("Mute Microphone")
  local speaker_btn = makeButton("Speaker Off")
  speaker_btn.setContentDescription("Speaker Off")
  ctrl_row_1.addView(mute_btn, LinearLayout.LayoutParams(0, -2, 1))
  ctrl_row_1.addView(speaker_btn, LinearLayout.LayoutParams(0, -2, 1))
  layout.addView(ctrl_row_1)

  local add_person_btn = makeButton("Add Person to Call")
  layout.addView(add_person_btn, LinearLayout.LayoutParams(-1, -2))

  local end_call_btn = makeButton("End Call")
  end_call_btn.setBackgroundColor(0xFFD32F2F)
  end_call_btn.setTextColor(0xFFFFFFFF)
  layout.addView(end_call_btn, LinearLayout.LayoutParams(-1, -2))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Live Voice Call - " .. call_label)
    .setView(layout)
    .setCancelable(false)
    .create()
  active_call_dialog = dialog
  dialog.show()

  local call_active = true
  local connected_sound_played = false
  local call_opened_epoch = os.time()
  local poll_handler = Handler(Looper.getMainLooper())
  local poll_runnable = nil

  local dial_loop_mp = nil
  local dial_stop_handler = Handler(Looper.getMainLooper())
  local dial_stop_runnable = nil

  local function stopDialLoopSound()
    if dial_stop_runnable then
      pcall(function() dial_stop_handler.removeCallbacks(dial_stop_runnable) end)
      dial_stop_runnable = nil
    end
    if dial_loop_mp ~= nil then
      pcall(function()
        if dial_loop_mp.isPlaying() then dial_loop_mp.stop() end
        dial_loop_mp.release()
      end)
      dial_loop_mp = nil
    end
  end

  if start_dial_loop then
    dial_loop_mp = playSound(SOUND_CALL_VOICEMAIL_LOOP, nil, ToneGenerator.TONE_SUP_PIP, true)
    dial_stop_runnable = Runnable({
      run = function()
        stopDialLoopSound()
      end
    })
    dial_stop_handler.postDelayed(dial_stop_runnable, 15000)
  end

  local function triggerConnectedSoundOnce()
    if not connected_sound_played then
      connected_sound_played = true
      stopDialLoopSound()
      playSound(SOUND_CALL_CONNECTED, nil, ToneGenerator.TONE_PROP_ACK, false)
    end
  end

  local function finishCallCleanup()
    call_active = false
    stopDialLoopSound()
    active_call_dialog = nil
    active_call_id = nil
    active_call_is_muted = false
    pcall(function()
      rtc_webview.evaluateJavascript("if(window.stopLiveWebRtc) window.stopLiveWebRtc();", nil)
      rtc_webview.destroy()
    end)
    if poll_runnable then
      pcall(function() poll_handler.removeCallbacks(poll_runnable) end)
      poll_runnable = nil
    end
    resetCallAudioMode()
  end

  local function leaveOrEndCall(reason_msg)
    stopDialLoopSound()
    http_delete(FIREBASE_URL .. "voice_calls/" .. call_id .. "/participants/" .. encodeKey(current_username) .. ".json", function() end)
    http_delete(FIREBASE_URL .. "voice_calls/" .. call_id .. "/muted/" .. encodeKey(current_username) .. ".json", function() end)
    if call_type == "direct" then
      http_post_or_put(FIREBASE_URL .. "voice_calls/" .. call_id .. "/status.json", "PUT", "ended", function() end)
    end
    finishCallCleanup()
    pcall(function() dialog.dismiss() end)
    showToast(reason_msg or "Call ended.")
  end

  end_call_btn.setOnClickListener(function()
    leaveOrEndCall("Call ended.")
  end)

  mute_btn.setOnClickListener(function()
    active_call_is_muted = not active_call_is_muted
    setCallAudioMode(active_call_speaker_on, active_call_is_muted)
    pcall(function()
      rtc_webview.evaluateJavascript("if(window.setMicMuteState) window.setMicMuteState(" .. tostring(active_call_is_muted) .. ");", nil)
    end)
    local mLbl = active_call_is_muted and "Unmute Microphone" or "Mute Microphone"
    mute_btn.setText(mLbl)
    mute_btn.setContentDescription(mLbl)
    http_post_or_put(FIREBASE_URL .. "voice_calls/" .. call_id .. "/muted/" .. encodeKey(current_username) .. ".json", "PUT", active_call_is_muted, function() end)
    showToast(active_call_is_muted and "Microphone muted." or "Microphone unmuted.")
  end)

  speaker_btn.setOnClickListener(function()
    active_call_speaker_on = not active_call_speaker_on
    setCallAudioMode(active_call_speaker_on, active_call_is_muted)
    local sLbl = active_call_speaker_on and "Speaker Off" or "Speaker On"
    speaker_btn.setText(sLbl)
    speaker_btn.setContentDescription(sLbl)
    showToast(active_call_speaker_on and "Speaker on." or "Earpiece mode.")
  end)

  add_person_btn.setOnClickListener(function()
    http_get(FIREBASE_URL .. "registered_users.json", function(s_u, r_u)
      http_get(FIREBASE_URL .. "user_presence.json", function(s_p, r_p)
        local online_candidates = {}
        local pdata = {}
        if s_p and r_p and r_p ~= "null" then
          local ok_p, dec_p = pcall(cjson.decode, r_p)
          if ok_p and type(dec_p) == "table" then pdata = dec_p end
        end
        local now = os.time()
        if s_u and r_u and r_u ~= "null" then
          local ok_u, udata = pcall(cjson.decode, r_u)
          if ok_u and type(udata) == "table" then
            for k, v in pairs(udata) do
              local uname = (type(v) == "table" and v.username) or k
              if uname and uname ~= "" and trim(uname):lower() ~= trim(current_username):lower() then
                local pe = pdata[encodeKey(uname)] or pdata[uname]
                if type(pe) == "table" and pe.status == "online" and (now - tonumber(pe.time_epoch or 0) < 240) then
                  table.insert(online_candidates, uname)
                end
              end
            end
          end
        end
        if #online_candidates == 0 then
          showToast("No other online users available to add.")
          return
        end
        AlertDialog.Builder(activity)
          .setTitle("Add Online Person to Call")
          .setItems(online_candidates, DialogInterface.OnClickListener{
            onClick = function(_, w)
              local invite_user = online_candidates[w + 1]
              http_post_or_put(FIREBASE_URL .. "voice_calls/" .. call_id .. "/invited/" .. encodeKey(invite_user) .. ".json", "PUT", invite_user, function()
                http_post_or_put(FIREBASE_URL .. "voice_calls/" .. call_id .. "/participants/" .. encodeKey(invite_user) .. ".json", "PUT", invite_user, function()
                  showToast("Added " .. invite_user .. " to live call!")
                end)
              end)
            end
          }).show()
      end)
    end)
  end)

  local function refreshCallState()
    if not call_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "voice_calls/" .. call_id .. ".json", function(s, r)
      if not call_active then return end
      if not s or not r or r == "null" then
        finishCallCleanup()
        pcall(function() dialog.dismiss() end)
        return
      end
      local ok, cdata = pcall(cjson.decode, r)
      if not ok or type(cdata) ~= "table" then return end

      local c_status = tostring(cdata.status or "")
      if c_status == "ended" then
        finishCallCleanup()
        pcall(function() dialog.dismiss() end)
        showToast("Call ended.")
        return
      end

      if c_status == "ringing" and start_dial_loop and (os.time() - call_opened_epoch) >= CALL_RING_TIMEOUT_SEC then
        leaveOrEndCall("Call not answered")
        return
      end

      local part_names = {}
      local muted_map = type(cdata.muted) == "table" and cdata.muted or {}
      if type(cdata.participants) == "table" then
        for pk, pv in pairs(cdata.participants) do
          local pname = type(pv) == "string" and pv or Uri.decode(tostring(pk))
          local is_m = (muted_map[encodeKey(pname)] == true or muted_map[pname] == true)
          local tag = pname
          if is_m then tag = tag .. " [Muted]" end
          table.insert(part_names, tag)
        end
      end
      if #part_names == 0 then
        table.insert(part_names, current_username)
      end
      participants_tv.setText("In Live Call: " .. table.concat(part_names, ", "))

      if c_status == "active" or call_type == "room_live" then
        triggerConnectedSoundOnce()
        status_tv.setText("Live Connected (" .. call_label .. ")")
      else
        status_tv.setText("Ringing " .. call_label .. "...")
      end
    end)
  end

  refreshCallState()

  poll_runnable = Runnable({
    run = function()
      if call_active then
        refreshCallState()
        poll_handler.postDelayed(poll_runnable, CALL_POLL_INTERVAL_MS)
      end
    end
  })
  poll_handler.postDelayed(poll_runnable, CALL_POLL_INTERVAL_MS)
end

local function initiateVoiceCall(call_type, target_or_id, title_label, member_list)
  if notifyServerDownIfNeeded() then return end

  local function launchCallRecord()
    local call_id = "call_" .. tostring(os.time()) .. "_" .. tostring(math.random(100, 999))
    local parts = {}
    parts[encodeKey(current_username)] = current_username
    local invited = {}

    if call_type == "direct" then
      invited[encodeKey(target_or_id)] = target_or_id
    elseif type(member_list) == "table" then
      for _, mname in ipairs(member_list) do
        if trim(tostring(mname)):lower() ~= trim(current_username):lower() then
          invited[encodeKey(mname)] = mname
        end
      end
    end

    local call_payload = {
      id = call_id,
      call_type = call_type,
      caller = current_username,
      target = target_or_id,
      title = title_label,
      status = (call_type == "room_live") and "active" or "ringing",
      created_epoch = os.time(),
      participants = parts,
      invited = invited
    }

    http_post_or_put(FIREBASE_URL .. "voice_calls/" .. call_id .. ".json", "PUT", call_payload, function(ok)
      if ok then
        if call_type == "room_live" then
          local live_notice = {
            id = call_id,
            caller = current_username,
            title = title_label,
            created_epoch = os.time()
          }
          http_post_or_put(FIREBASE_URL .. "settings/room_live_voice.json", "PUT", live_notice, function() end)
          openActiveCallSessionDialog(call_id, call_payload, false)
        else
          openActiveCallSessionDialog(call_id, call_payload, true)
        end
      else
        showToast("Unable to start voice call.")
      end
    end)
  end

  if call_type == "direct" then
    isUserCurrentlyOnline(target_or_id, function(is_on)
      if not is_on then
        showOfflineCallDialog(getVerifiedName(target_or_id))
        return
      end
      launchCallRecord()
    end)
  else
    launchCallRecord()
  end
end

function stopIncomingCallWatcher()
  if incoming_call_handler ~= nil and incoming_call_runnable ~= nil then
    pcall(function()
      incoming_call_handler.removeCallbacks(incoming_call_runnable)
    end)
  end
  incoming_call_handler = nil
  incoming_call_runnable = nil
end

local function startIncomingCallWatcher()
  if incoming_call_handler ~= nil or not isAppForeground then return end
  incoming_call_handler = Handler(Looper.getMainLooper())
  incoming_call_runnable = Runnable({
    run = function()
      if not isAppForeground then
        stopIncomingCallWatcher()
        return
      end

      if current_username ~= "" and active_call_dialog == nil and isNetworkAvailable() then
        http_get(FIREBASE_URL .. "voice_calls.json?shallow=true", function(s_sh, r_sh)
          if not isAppForeground or active_call_dialog ~= nil then return end
          if s_sh and r_sh and r_sh ~= "null" then
            local ok_sh, keys_map = pcall(cjson.decode, r_sh)
            if ok_sh and type(keys_map) == "table" and table_size(keys_map) > 0 then
              local now = os.time()
              local my_norm = trim(current_username):lower()
              for cid, _ in pairs(keys_map) do
                local ep_str = tostring(cid):match("^call_(%d+)_")
                local ep_num = tonumber(ep_str or 0)
                if ep_num > 0 and (now - ep_num) < (CALL_RING_TIMEOUT_SEC + 10) then
                  http_get(FIREBASE_URL .. "voice_calls/" .. tostring(cid) .. ".json", function(s, r)
                    if not isAppForeground or active_call_dialog ~= nil then return end
                    if s and r and r ~= "null" then
                      local ok, cdata = pcall(cjson.decode, r)
                      if ok and type(cdata) == "table" and tostring(cdata.call_type or "") ~= "room_live" and tostring(cdata.status or "") == "ringing" and (os.time() - tonumber(cdata.created_epoch or 0) < CALL_RING_TIMEOUT_SEC) then
                        local is_invited = false
                        if type(cdata.invited) == "table" then
                          for ik, iv in pairs(cdata.invited) do
                            local iname = type(iv) == "string" and iv or Uri.decode(tostring(ik))
                            if trim(iname):lower() == my_norm then
                              is_invited = true
                              break
                            end
                          end
                        end
                        if is_invited and trim(tostring(cdata.caller or "")):lower() ~= my_norm then
                          local ctype = tostring(cdata.call_type or "direct")
                          local caller_name = tostring(cdata.caller or "User")
                          local ctitle = tostring(cdata.title or caller_name)
                          local ring_mp = playSound(SOUND_GROUP_CALL_RING, nil, ToneGenerator.TONE_SUP_RINGTONE, false)

                          local function stopIncomingRing()
                            if ring_mp ~= nil then
                              pcall(function()
                                if ring_mp.isPlaying() then ring_mp.stop() end
                                ring_mp.release()
                              end)
                              ring_mp = nil
                            end
                          end

                          local call_prompt_msg = (ctype == "group")
                            and ("Incoming Live Group Call from " .. getVerifiedName(caller_name) .. " in group: " .. ctitle)
                            or ("Incoming Live Voice Call from " .. getVerifiedName(caller_name))

                          AlertDialog.Builder(activity)
                            .setTitle(ctype == "group" and "Incoming Group Call" or "Incoming Voice Call")
                            .setMessage(call_prompt_msg)
                            .setCancelable(false)
                            .setPositiveButton("Answer Call", DialogInterface.OnClickListener{
                              onClick = function()
                                stopIncomingRing()
                                playSound(SOUND_CALL_CONNECTED, nil, ToneGenerator.TONE_PROP_ACK, false)
                                http_post_or_put(FIREBASE_URL .. "voice_calls/" .. cid .. "/participants/" .. encodeKey(current_username) .. ".json", "PUT", current_username, function()
                                  http_post_or_put(FIREBASE_URL .. "voice_calls/" .. cid .. "/status.json", "PUT", "active", function()
                                    openActiveCallSessionDialog(cid, cdata, false)
                                  end)
                                end)
                              end
                            })
                            .setNegativeButton("End Call", DialogInterface.OnClickListener{
                              onClick = function()
                                stopIncomingRing()
                                http_delete(FIREBASE_URL .. "voice_calls/" .. cid .. "/invited/" .. encodeKey(current_username) .. ".json", function() end)
                                if ctype == "direct" then
                                  http_post_or_put(FIREBASE_URL .. "voice_calls/" .. cid .. "/status.json", "PUT", "ended", function() end)
                                end
                              end
                            })
                            .show()
                        end
                      end
                    end
                  end)
                end
              end
            end
          end
        end)
      end

      if isAppForeground and incoming_call_handler and incoming_call_runnable then
        incoming_call_handler.postDelayed(incoming_call_runnable, 10000)
      end
    end
  })
  incoming_call_handler.postDelayed(incoming_call_runnable, 5000)
endend
-- ========================================================
-- BTP ASSISTANT ENGINE & PERSONAL AUTO-REPLY SYSTEM
-- ========================================================

local assistantTaskCounter = 0
_G.BtpAssistantAudioCallbacks = {}

function onBtpAssistantAudioDone(taskId, success, outPath)
  local cb = _G.BtpAssistantAudioCallbacks[taskId]
  if cb then
    _G.BtpAssistantAudioCallbacks[taskId] = nil
    cb(success, outPath)
  end
end

local function stripAssistantMarkdownEmojis(str)
  local s = tostring(str or "")
  s = s:gsub("```.-```", " Code block generated. ")
  s = s:gsub("[\240-\244][\128-\191][\128-\191][\128-\191]", "")
  s = s:gsub("[%*%#`_~]", " ")
  s = s:gsub("%s+", " "):gsub("^%s*(.-)%s*$", "%1")
  return s
end

local function enforceBtpAssistantIdentity(replyStr)
  local s = tostring(replyStr or "")
  s = s:gsub("[Cc][Hh][Aa][Tt]%s*[Gg][Pp][Tt]", "BTP Assistant")
  s = s:gsub("[Oo][Pp][Ee][Nn]%s*[Aa][Ii]", "Blind Tech Power Hub")
  s = s:gsub("[Gg][Pp][Tt]%-%d+[%w%.]*", "BTP Assistant")
  return s
end

local function splitAssistantChunks(str, maxLen)
  local chunks = {}
  local clean = stripAssistantMarkdownEmojis(str)
  while string.len(clean) > 0 do
    if string.len(clean) <= maxLen then
      table.insert(chunks, clean)
      break
    end
    local cutPos = maxLen
    local spacePos = clean:sub(1, maxLen):match(".*()%s")
    if spacePos and spacePos > 40 then
      cutPos = spacePos
    end
    local piece = trim(clean:sub(1, cutPos))
    if piece ~= "" then
      table.insert(chunks, piece)
    end
    clean = trim(clean:sub(cutPos + 1))
  end
  return chunks
end

local function generateAssistantSpeechFile(text, langCode, outPath, callback)
  assistantTaskCounter = assistantTaskCounter + 1
  local tId = "btp_ast_" .. tostring(assistantTaskCounter)
  _G.BtpAssistantAudioCallbacks[tId] = callback

  local chunks = splitAssistantChunks(text, 170)
  if #chunks == 0 then
    callback(false, outPath)
    return
  end

  local encodedChunks = {}
  for _, c in ipairs(chunks) do
    table.insert(encodedChunks, URLEncoder.encode(c, "UTF-8"))
  end
  local joined = table.concat(encodedChunks, "|||")
  local tl = langCode or "hi"

  thread(function(tid, encStr, lang, dest)
    require "import"
    import "java.net.*"
    import "java.io.*"

    local okRun, written = pcall(function()
      local fos = FileOutputStream(dest)
      local total = 0
      for part in string.gmatch(encStr, "([^|||]+)") do
        local u = URL("https://translate.google.com/translate_tts?ie=UTF-8&client=tw-ob&tl=" .. lang .. "&q=" .. part)
        local conn = u.openConnection()
        conn.setRequestProperty("User-Agent", "Mozilla/5.0 (Linux; Android 10) AppleWebKit/537.36")
        conn.setConnectTimeout(10000)
        conn.setReadTimeout(15000)
        if conn.getResponseCode() == 200 then
          local inp = conn.getInputStream()
          local buf = byte[4096]
          local n = inp.read(buf)
          while n ~= -1 do
            fos.write(buf, 0, n)
            total = total + n
            n = inp.read(buf)
          end
          inp.close()
        end
      end
      fos.flush()
      fos.close()
      return total
    end)

    call("onBtpAssistantAudioDone", tid, (okRun and (tonumber(written) or 0) > 150), dest)
  end, tId, joined, tl, outPath)
end

local function buildTrainedKnowledgeContext(queryStr, extra_list)
  local combined = {}
  if type(extra_list) == "table" then
    for _, it in ipairs(extra_list) do table.insert(combined, it) end
  end
  if type(assistant_trained_items) == "table" then
    for _, it in ipairs(assistant_trained_items) do table.insert(combined, it) end
  end
  if #combined == 0 then
    return ""
  end
  local qLow = trim(tostring(queryStr or "")):lower()
  local out = {}
  for _, it in ipairs(combined) do
    local kLow = trim(tostring(it.q or "")):lower()
    if kLow ~= "" and (qLow == "" or qLow:find(kLow, 1, true) or kLow:find(qLow, 1, true)) then
      table.insert(out, tostring(it.q or "") .. ": " .. tostring(it.a or ""))
      if #out >= 3 then break end
    end
  end
  if #out == 0 then
    for i = 1, math.min(2, #combined) do
      local it = combined[i]
      table.insert(out, tostring(it.q or "") .. ": " .. tostring(it.a or ""))
    end
  end
  return table.concat(out, " | ")
end

local function findLocalTrainedAnswer(queryStr, extra_list)
  local qLow = trim(tostring(queryStr or "")):lower()
  if qLow == "" then return nil end

  if type(extra_list) == "table" then
    for _, item in ipairs(extra_list) do
      local kLow = trim(tostring(item.q or "")):lower()
      if kLow ~= "" and (qLow == kLow or qLow:find(kLow, 1, true)) then
        return tostring(item.a or "")
      end
    end
  end

  for _, item in ipairs(assistant_trained_items) do
    local kLow = trim(tostring(item.q or "")):lower()
    if kLow ~= "" and (qLow == kLow or qLow:find(kLow, 1, true)) then
      return tostring(item.a or "")
    end
  end

  if qLow == "hi" or qLow == "hello" or qLow == "namaste" or qLow == "salam" or qLow == "assalamualaikum" then
    return "Namaste " .. ((current_username ~= "" and current_username) or "Dost") .. "! Main BTP Assistant hoon. Aap mujhse AndroLua code, app features, ya koi bhi sawal poochh sakte hain."
  elseif qLow:find("tum kaun ho", 1, true) or qLow:find("who are you", 1, true) or qLow:find("apna naam", 1, true) or qLow:find("your name", 1, true) or qLow:find("tumhara naam", 1, true) or qLow:find("naam kya", 1, true) then
    return "Mera naam BTP Assistant hai. Mujhe Ibrahim Ansari ne Blind Tech Power Hub ke liye banaya hai."
  elseif qLow:find("developer", 1, true) or qLow:find("kisne banaya", 1, true) then
    return "Is app aur BTP Assistant ko Ibrahim Ansari ne develop kiya hai."
  elseif qLow:find("version", 1, true) then
    return "Aap abhi version " .. CURRENT_VERSION .. " istemal kar rahe hain."
  end
  return nil
end

local function isFeedbackRequestText(queryStr)
  local l = trim(tostring(queryStr or "")):lower()
  return (l:find("feedback", 1, true) ~= nil or l:find("sugjav", 1, true) ~= nil or l:find("sujhav", 1, true) or l:find("report", 1, true) ~= nil)
end

local function submitAssistantFeedbackToFirebase(userName, feedbackText, onDone)
  local entry = {
    user = userName,
    message = feedbackText,
    timestamp = os.date("%I:%M %p, %d %b"),
    timestamp_raw = os.date("%Y%m%d%H%M%S")
  }
  http_post_or_put(FIREBASE_URL .. "settings/assistant_feedbacks.json", "POST", entry, function(ok)
    if onDone then onDone(ok) end
  end)
end

local function sanitizeAiResponseText(rawTxt)
  local t = trim(tostring(rawTxt or ""))
  if t == "" then return "" end
  local ok, parsed = pcall(cjson.decode, t)
  if ok and type(parsed) == "table" then
    t = parsed.reply or parsed.response or parsed.message or parsed.text or parsed.answer or ""
    t = trim(tostring(t))
  end
  local low = t:lower()
  if low == "" or low == "null" or low:find("<!doctype html", 1, true) or low:find("<html", 1, true) or low:find("error 5", 1, true) or low:find("rate limit", 1, true) then
    return ""
  end
  return enforceBtpAssistantIdentity(t)
end

local function fetchAssistantReplyWithFallback(modelObj, promptText, fallbackQuery, callback, extra_trained)
  local matchedLocal = findLocalTrainedAnswer(fallbackQuery, extra_trained)
  if matchedLocal and matchedLocal ~= "" then
    callback(true, enforceBtpAssistantIdentity(matchedLocal))
    return
  end

  if not isNetworkAvailable() then
    callback(false, "")
    return
  end

  local mId = (modelObj and modelObj.backendId) or "gemini-flash"
  local identityGuard = "STRICT RULE: Your name is BTP Assistant, created by Ibrahim Ansari for Blind Tech Power Hub. NEVER say you are ChatGPT or OpenAI. "
  local fullPrompt = identityGuard .. promptText
  local encodedPrompt = URLEncoder.encode(fullPrompt, "UTF-8")
  local encodedRawQ = URLEncoder.encode(identityGuard .. "User asks: " .. tostring(fallbackQuery or promptText):sub(1, 250), "UTF-8")

  local url1 = "https://ai-hub.schoolofmindlight.workers.dev/?model=" .. URLEncoder.encode(mId, "UTF-8") .. "&chat=" .. encodedPrompt
  Http.get(url1, nil, "UTF-8", nil, function(code1, content1)
    local r1 = (code1 == 200) and sanitizeAiResponseText(content1) or ""
    if r1 ~= "" then
      callback(true, r1)
      return
    end

    local url2 = "https://text.pollinations.ai/" .. encodedRawQ
    Http.get(url2, nil, "UTF-8", nil, function(code2, content2)
      local r2 = (code2 == 200) and sanitizeAiResponseText(content2) or ""
      if r2 ~= "" then
        callback(true, r2)
        return
      end

      local url3 = "https://ai-hub.schoolofmindlight.workers.dev/?model=gemini-flash&chat=" .. encodedRawQ
      Http.get(url3, nil, "UTF-8", nil, function(code3, content3)
        local r3 = (code3 == 200) and sanitizeAiResponseText(content3) or ""
        if r3 ~= "" then
          callback(true, r3)
        else
          callback(false, "")
        end
      end)
    end)
  end)
end

-- ========================================================
-- PERSONAL CHAT ASSISTANT SETUP & TRAINING (ALL USERS)
-- ========================================================

function showPersonalAssistantSetupDialog()
  if current_username == "" then
    showToast("Please login first.")
    return
  end

  local layout = makeLayout(true, 14)
  local is_enabled = sp.getBoolean("personal_ast_enabled", false)
  local away_msg = tostring(sp.getString("personal_ast_away_msg", "Main abhi offline hoon, meri jagah BTP Assistant reply kar raha hai."))
  local raw_personal_train = tostring(sp.getString("personal_ast_training_json", "[]"))
  local ok_pt, personal_train_list = pcall(cjson.decode, raw_personal_train)
  if not ok_pt or type(personal_train_list) ~= "table" then
    personal_train_list = {}
  end

  local status_tv = makeText("Personal Chat Assistant: " .. (is_enabled and "ACTIVE (ON)" or "INACTIVE (OFF)"), 15)
  status_tv.setTextColor(is_enabled and 0xFF2E7D32 or 0xFFD32F2F)
  layout.addView(status_tv)

  layout.addView(makeText("Jab aap offline honge, tab aapki personal chat mein BTP Assistant automatically reply karega. Online aate hi auto-reply band ho jayega.", 12))

  local toggle_btn = makeButton(is_enabled and "Turn OFF Personal Assistant" or "Turn ON Personal Assistant")
  layout.addView(toggle_btn)

  local away_inp = EditText(activity)
  away_inp.setHint("Custom Offline Greeting / Away Note")
  away_inp.setText(away_msg)
  layout.addView(away_inp)

  layout.addView(makeText("Train Your Personal Assistant (Add Custom Q&A):", 14))
  local q_inp = EditText(activity)
  q_inp.setHint("Agar koi yeh poochhe (e.g. kahan ho, number do)")
  local a_inp = EditText(activity)
  a_inp.setHint("Toh assistant yeh jawab de")
  a_inp.setMinLines(2)
  layout.addView(q_inp)
  layout.addView(a_inp)

  local add_qa_btn = makeButton("Add Training Q&A")
  layout.addView(add_qa_btn)

  local list_tv = makeText("", 12)
  local sc = ScrollView(activity)
  sc.addView(list_tv)
  layout.addView(sc, LinearLayout.LayoutParams(-1, 180))

  local function refreshTrainPreview()
    if #personal_train_list == 0 then
      list_tv.setText("No personal training added yet.")
    else
      local lines = {}
      for i, item in ipairs(personal_train_list) do
        table.insert(lines, tostring(i) .. ". Q: " .. tostring(item.q or "") .. "\n    A: " .. tostring(item.a or ""))
      end
      list_tv.setText(table.concat(lines, "\n\n"))
    end
  end
  refreshTrainPreview()

  local function syncPersonalAssistantToFirebase(enabled_state)
    local clean_away = trim(away_inp.getText())
    if clean_away == "" then
      clean_away = "Main abhi offline hoon, meri jagah BTP Assistant reply kar raha hai."
    end
    sp.edit()
      .putBoolean("personal_ast_enabled", enabled_state)
      .putString("personal_ast_away_msg", clean_away)
      .putString("personal_ast_training_json", cjson.encode(personal_train_list))
      .apply()

    local fb_payload = {
      enabled = enabled_state,
      away_message = clean_away,
      training = personal_train_list,
      updated_epoch = os.time()
    }
    http_post_or_put(FIREBASE_URL .. "personal_assistants/" .. encodeKey(current_username) .. ".json", "PUT", fb_payload, function() end)
  end

  toggle_btn.setOnClickListener(function()
    is_enabled = not is_enabled
    status_tv.setText("Personal Chat Assistant: " .. (is_enabled and "ACTIVE (ON)" or "INACTIVE (OFF)"))
    status_tv.setTextColor(is_enabled and 0xFF2E7D32 or 0xFFD32F2F)
    toggle_btn.setText(is_enabled and "Turn OFF Personal Assistant" or "Turn ON Personal Assistant")
    syncPersonalAssistantToFirebase(is_enabled)
    showToast(is_enabled and "Personal Chat Assistant Activated!" or "Personal Chat Assistant Turned OFF.")
  end)

  add_qa_btn.setOnClickListener(function()
    local qt = trim(q_inp.getText())
    local at = trim(a_inp.getText())
    if qt == "" or at == "" then
      showToast("Question aur Answer dono likhein.")
      return
    end
    table.insert(personal_train_list, { q = qt, a = at })
    q_inp.setText("")
    a_inp.setText("")
    refreshTrainPreview()
    syncPersonalAssistantToFirebase(is_enabled)
    showToast("Personal Assistant trained!")
  end)

  AlertDialog.Builder(activity)
    .setTitle("Personal Chat BTP Assistant")
    .setView(layout)
    .setPositiveButton("Save & Close", DialogInterface.OnClickListener{
      onClick = function()
        syncPersonalAssistantToFirebase(is_enabled)
      end
    })
    .setNegativeButton("Clear Training", DialogInterface.OnClickListener{
      onClick = function()
        personal_train_list = {}
        syncPersonalAssistantToFirebase(is_enabled)
        showToast("Personal training cleared.")
      end
    })
    .show()
end

local function openAssistantLiveVoiceDialog()
  if assistant_is_locked and not isDeveloper(current_username) then
    showMessage("BTP Assistant", "Assistant is currently locked.")
    return
  end

  local uname = (current_username ~= "" and current_username) or "User"
  local isLive = true
  local isMuted = false
  local liveRec = nil
  local liveMp = nil
  local turnCnt = 0

  playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)

  local box = makeLayout(true, 16)
  box.addView(makeText("BTP Assistant Live Voice Mode", 19))
  box.addView(makeText("Speak naturally with BTP Assistant. Tap Mute or Close anytime.", 13))

  local statusTv = makeText("Status: Connecting...", 15)
  statusTv.setTextColor(0xFF0D47A1)
  statusTv.setPadding(0, 8, 0, 8)
  box.addView(statusTv)

  local logTv = makeText("Ready to listen.", 14)
  logTv.setPadding(12, 12, 12, 14)
  logTv.setBackgroundColor(0xFFE8F5E9)
  box.addView(logTv)

  local muteBtn = makeButton("Mute Microphone")
  muteBtn.setContentDescription("Mute Microphone")
  box.addView(muteBtn, LinearLayout.LayoutParams(-1, -2))

  local function stopLiveMic()
    pcall(function()
      if liveRec then
        liveRec.setRecognitionListener(nil)
        liveRec.cancel()
        liveRec.destroy()
        liveRec = nil
      end
    end)
  end

  local function stopLiveMp()
    pcall(function()
      if liveMp then
        if liveMp.isPlaying() then liveMp.stop() end
        liveMp.release()
        liveMp = nil
      end
    end)
  end

  local startLiveMicLoop

  local function speakLiveReply(txt)
    if not isLive then return end
    local clean = stripAssistantMarkdownEmojis(enforceBtpAssistantIdentity(txt))
    statusTv.setText("Status: Speaking...")
    logTv.setText("BTP Assistant: " .. clean)
    turnCnt = turnCnt + 1
    local outP = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_live_" .. tostring(turnCnt) .. ".mp3"
    generateAssistantSpeechFile(clean, "hi", outP, function(ok, savedP)
      if not isLive then return end
      if ok then
        stopLiveMp()
        local pOk = pcall(function()
          liveMp = MediaPlayer()
          liveMp.setDataSource(savedP)
          liveMp.prepare()
          liveMp.start()
          liveMp.setOnCompletionListener(MediaPlayer.OnCompletionListener{
            onCompletion = function()
              stopLiveMp()
              if isLive and not isMuted then
                Handler(Looper.getMainLooper()).postDelayed(Runnable{
                  run = function() startLiveMicLoop() end
                }, 400)
              end
            end
          })
        end)
        if not pOk and isLive and not isMuted then
          startLiveMicLoop()
        end
      elseif isLive and not isMuted then
        startLiveMicLoop()
      end
    end)
  end

  startLiveMicLoop = function()
    if (not isLive) or isMuted or not isNetworkAvailable() then return end
    stopLiveMic()
    statusTv.setText("Status: Listening...")
    pcall(function()
      liveRec = SpeechRecognizer.createSpeechRecognizer(activity)
      local it = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH)
      it.putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
      it.putExtra(RecognizerIntent.EXTRA_LANGUAGE, "hi-IN")
      it.putExtra(RecognizerIntent.EXTRA_PARTIAL_RESULTS, false)
      liveRec.setRecognitionListener(RecognitionListener{
        onReadyForSpeech = function() if isLive and not isMuted then statusTv.setText("Status: Speak now...") end end,
        onBeginningOfSpeech = function() end,
        onRmsChanged = function() end,
        onBufferReceived = function() end,
        onEndOfSpeech = function() end,
        onError = function()
          if isLive and not isMuted then
            Handler(Looper.getMainLooper()).postDelayed(Runnable{
              run = function() startLiveMicLoop() end
            }, 600)
          end
        end,
        onResults = function(res)
          local matches = res.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
          local spoken = (matches and matches.size() > 0) and tostring(matches.get(0)) or ""
          if spoken == "" then
            if isLive and not isMuted then startLiveMicLoop() end
            return
          end
          logTv.setText(uname .. ": " .. spoken)
          statusTv.setText("Status: Thinking...")
          local trainedCtx = buildTrainedKnowledgeContext(spoken)
          local prompt = "You are BTP Assistant (" .. APP_TITLE .. "). " .. (trainedCtx ~= "" and (trainedCtx .. ". ") or "") .. "Q: " .. spoken .. " (Short clear answer, no emojis)"
          fetchAssistantReplyWithFallback({backendId = "gemini-flash"}, prompt, spoken, function(ok, reply)
            if not isLive then return end
            if ok and reply ~= "" then
              speakLiveReply(reply)
            else
              speakLiveReply("Abhi network slow hai, kripya ek baar phir boliye.")
            end
          end)
        end,
        onPartialResults = function() end,
        onEvent = function() end
      })
      liveRec.startListening(it)
    end)
  end

  muteBtn.setOnClickListener(function()
    isMuted = not isMuted
    if isMuted then
      stopLiveMic()
      muteBtn.setText("Unmute Microphone")
      muteBtn.setContentDescription("Unmute Microphone")
      statusTv.setText("Status: Microphone Muted")
    else
      muteBtn.setText("Mute Microphone")
      muteBtn.setContentDescription("Mute Microphone")
      startLiveMicLoop()
    end
  end)

  local dlg = AlertDialog.Builder(activity)
    .setTitle("BTP Assistant Live")
    .setView(box)
    .setCancelable(false)
    .setNegativeButton("End Live Mode", DialogInterface.OnClickListener{
      onClick = function()
        isLive = false
        stopLiveMic()
        stopLiveMp()
      end
    })
    .create()
  dlg.show()

  Handler(Looper.getMainLooper()).postDelayed(Runnable{
    run = function()
      if isLive then
        speakLiveReply("Hello " .. uname .. ", main BTP Assistant hoon. Kuchh bhi poochhiye.")
      end
    end
  }, 800)
end

function openBTPAssistantDialog()
  if notifyServerDownIfNeeded() then return end

  local uname = (current_username ~= "" and current_username) or "User"
  local ast_models = {
    {displayName = "BTP Flash (Fast)", backendId = "gemini-flash"},
    {displayName = "BTP 1.4 (Default)", backendId = "gpt-sol"},
    {displayName = "Blind Tech Power Pro", backendId = "gpt-5.5"},
    {displayName = "BTP Ultra 2.0", backendId = "claude-sonnet"},
    {displayName = "BTP Vision & Smart", backendId = "gemini-pro"}
  }
  local model_idx = sp.getInt("btp_ast_model_idx", 1)
  local mem_enabled = sp.getBoolean("btp_ast_mem_on", true)
  local auto_tts = sp.getBoolean("btp_ast_auto_tts", false)
  local saved_mem = tostring(sp.getString("btp_ast_memory", ""))
  local chatHistory = {}
  if mem_enabled and saved_mem ~= "" then
    table.insert(chatHistory, saved_mem:sub(-240))
  end

  local astPlayer = nil
  local activeListenBtn = nil
  local replySeq = 0
  local isGenerating = false
  local reqSeq = 0
  local isMicBusy = false
  local micRec = nil
  local awaitingFeedbackInput = false

  playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)

  local root = makeLayout(true, 14)

  local topBar = makeLayout(false, 4)
  topBar.setGravity(Gravity.CENTER_VERTICAL)
  local titleTv = makeText("BTP Assistant", 18)
  titleTv.setTextColor(0xFF0D47A1)
  topBar.addView(titleTv, LinearLayout.LayoutParams(0, -2, 1))

  local moreBtn = makeButton("More Options")
  topBar.addView(moreBtn, LinearLayout.LayoutParams(-2, -2))
  root.addView(topBar)

  local lockedBanner = makeText("Assistant is currently locked.", 14)
  lockedBanner.setTextColor(0xFFD32F2F)
  lockedBanner.setPadding(8, 8, 8, 8)
  lockedBanner.setVisibility(View.GONE)
  root.addView(lockedBanner)

  local chatScroll = ScrollView(activity)
  local chatContainer = makeLayout(true, 8)
  chatScroll.addView(chatContainer)
  root.addView(chatScroll, LinearLayout.LayoutParams(-1, 340))

  local statusTv = makeText("", 12)
  statusTv.setTextColor(0xFF1E88E5)
  statusTv.setVisibility(View.GONE)
  root.addView(statusTv)

  local function stopAstAudio()
    pcall(function()
      if astPlayer then
        if astPlayer.isPlaying() then astPlayer.stop() end
        astPlayer.release()
        astPlayer = nil
      end
    end)
    if activeListenBtn then
      pcall(function() activeListenBtn.setText("Listen") end)
      activeListenBtn = nil
    end
  end

  local function toggleAstAudio(filePath, btn)
    if activeListenBtn == btn and astPlayer ~= nil then
      stopAstAudio()
      return
    end
    stopAstAudio()
    local ok = pcall(function()
      astPlayer = MediaPlayer()
      astPlayer.setDataSource(filePath)
      astPlayer.prepare()
      astPlayer.start()
      activeListenBtn = btn
      btn.setText("Stop Listening")
      astPlayer.setOnCompletionListener(MediaPlayer.OnCompletionListener{
        onCompletion = function()
          stopAstAudio()
        end
      })
    end)
    if not ok then
      stopAstAudio()
      showToast("Unable to play voice.")
    end
  end

  local function extractLuaCode(txt)
    return txt:match("```[%w]*\n(.-)\n?```") or txt:match("```(.-)```")
  end

  local function appendAstBubble(sender, textStr, isReply, allowAutoPlay)
    if isReply then
      playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)
    end

    local bubble = makeLayout(true, 8)
    bubble.setBackgroundColor(isReply and 0xFFE8F5E9 or 0xFFE3F2FD)
    bubble.setPadding(12, 10, 12, 10)
    bubble.setFocusable(true)

    local finalTxt = isReply and enforceBtpAssistantIdentity(textStr) or tostring(textStr or "")
    local bodyTv = makeText(sender .. ":\n" .. finalTxt, 14)
    bodyTv.setTextIsSelectable(true)
    bubble.addView(bodyTv)

    if isReply then
      local row = makeLayout(false, 4)
      local listenBtn = makeButton("Preparing Voice...")
      listenBtn.setEnabled(false)
      row.addView(listenBtn)

      local codeSnippet = extractLuaCode(finalTxt)
      if codeSnippet and codeSnippet ~= "" then
        local copyBtn = makeButton("Copy Code")
        copyBtn.setOnClickListener(function()
          copyCode(codeSnippet)
        end)
        row.addView(copyBtn)
      end

      bubble.addView(row)

      replySeq = replySeq + 1
      local mp3Path = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_ast_reply_" .. tostring(replySeq) .. ".mp3"
      generateAssistantSpeechFile(finalTxt, "hi", mp3Path, function(ok, savedP)
        if ok then
          listenBtn.setText("Listen")
          listenBtn.setEnabled(true)
          listenBtn.setOnClickListener(function()
            toggleAstAudio(savedP, listenBtn)
          end)
          if allowAutoPlay and auto_tts then
            toggleAstAudio(savedP, listenBtn)
          end
        else
          listenBtn.setText("Retry Voice")
          listenBtn.setEnabled(true)
          listenBtn.setOnClickListener(function()
            generateAssistantSpeechFile(finalTxt, "hi", mp3Path, function(ok2, p2)
              if ok2 then
                listenBtn.setText("Listen")
                toggleAstAudio(p2, listenBtn)
              end
            end)
          end)
        end
      end)
    end

    chatContainer.addView(bubble, LinearLayout.LayoutParams(-1, -2))
    chatScroll.post(Runnable{
      run = function() chatScroll.fullScroll(ScrollView.FOCUS_DOWN) end
    })
  end

  local bottomRow = makeLayout(false, 4)
  bottomRow.setGravity(Gravity.CENTER_VERTICAL)

  local msgInput = EditText(activity)
  msgInput.setHint("Ask anything, type a question, or explore Lua...")
  bottomRow.addView(msgInput, LinearLayout.LayoutParams(0, -2, 1))

  local micBtn = makeButton("Microphone")
  micBtn.setContentDescription("Microphone")
  bottomRow.addView(micBtn, LinearLayout.LayoutParams(-2, -2))

  local sendBtn = makeButton("Send")
  bottomRow.addView(sendBtn, LinearLayout.LayoutParams(-2, -2))
  root.addView(bottomRow)

  local function refreshAssistantLockView()
    if assistant_is_locked and not isDeveloper(current_username) then
      lockedBanner.setVisibility(View.VISIBLE)
      bottomRow.setVisibility(View.GONE)
    else
      lockedBanner.setVisibility(View.GONE)
      bottomRow.setVisibility(View.VISIBLE)
    end
  end

  syncServerAndRoomSettings(function()
    refreshAssistantLockView()
  end)

  appendAstBubble("BTP Assistant", "Hello " .. uname .. "! Main BTP Assistant hoon. Chhote-mote sawal, app features, ya Lua ke baare mein poochhiye.", true, false)

  local function runAssistantQuery(userQuery)
    if notifyServerDownIfNeeded() then return end
    if assistant_is_locked and not isDeveloper(current_username) then
      refreshAssistantLockView()
      showToast("Assistant is currently locked.")
      return
    end

    if isGenerating then
      isGenerating = false
      reqSeq = reqSeq + 1
      statusTv.setVisibility(View.GONE)
      sendBtn.setText("Send")
      return
    end

    local q = trim(userQuery)
    if q == "" then return end

    playSound(SOUND_SEND, nil, ToneGenerator.TONE_PROP_BEEP, false)
    msgInput.setText("")
    appendAstBubble(uname, q, false, false)

    if awaitingFeedbackInput then
      awaitingFeedbackInput = false
      submitAssistantFeedbackToFirebase(uname, q, function(ok)
        if ok then
          appendAstBubble("BTP Assistant", "Aapka feedback receive ho gaya hai. Main isse admin/developer tak pahuncha dunga.", true, true)
        else
          appendAstBubble("BTP Assistant", "Feedback save karne mein problem aayi, kripya thodi der baad try karein.", true, false)
        end
      end)
      return
    end

    if isFeedbackRequestText(q) then
      awaitingFeedbackInput = true
      appendAstBubble("BTP Assistant", "Zaroor! Aap apna feedback yahan likh kar ya bol kar bhej sakte hain.", true, true)
      return
    end

    isGenerating = true
    reqSeq = reqSeq + 1
    local curReq = reqSeq
    sendBtn.setText("Stop")
    statusTv.setText("Thinking...")
    statusTv.setVisibility(View.VISIBLE)

    local chosenModel = ast_models[model_idx] or ast_models[1]
    local trainedCtx = buildTrainedKnowledgeContext(q)
    local recentCtx = (mem_enabled and #chatHistory > 0) and ("Prev: " .. table.concat(chatHistory, " | ") .. ". ") or ""
    local sysPrompt = "You are BTP Assistant in " .. APP_TITLE .. " built by Ibrahim Ansari. Never call yourself ChatGPT. "
      .. (trainedCtx ~= "" and ("Info: " .. trainedCtx .. ". ") or "")
      .. recentCtx
      .. "Q: " .. q .. "\nAnswer directly and concisely in clear Hindi/English without emojis."
    if #sysPrompt > 480 then sysPrompt = sysPrompt:sub(-480) end

    fetchAssistantReplyWithFallback(chosenModel, sysPrompt, q, function(ok, reply)
      if (not isGenerating) or (curReq ~= reqSeq) then return end
      isGenerating = false
      statusTv.setVisibility(View.GONE)
      sendBtn.setText("Send")

      if ok and reply ~= "" then
        local cleanReply = enforceBtpAssistantIdentity(trim(tostring(reply)))
        appendAstBubble("BTP Assistant", cleanReply, true, true)
        if mem_enabled then
          table.insert(chatHistory, q:sub(1, 60) .. " -> " .. cleanReply:sub(1, 80))
          if #chatHistory > 2 then
            table.remove(chatHistory, 1)
          end
          sp.edit().putString("btp_ast_memory", table.concat(chatHistory, " | ")).apply()
        end
      else
        appendAstBubble("BTP Assistant", "Abhi AI server busy hai. Kripya apna internet check karein ya 5 second baad dubara poochhiye.", true, false)
      end
    end)
  end

  sendBtn.setOnClickListener(function()
    runAssistantQuery(tostring(msgInput.getText()))
  end)

  micBtn.setOnClickListener(function()
    if assistant_is_locked and not isDeveloper(current_username) then
      refreshAssistantLockView()
      showToast("Assistant is currently locked.")
      return
    end
    if isMicBusy then
      isMicBusy = false
      micBtn.setText("Microphone")
      pcall(function() if micRec then micRec.cancel() micRec.destroy() micRec = nil end end)
      return
    end
    isMicBusy = true
    stopAstAudio()
    local okMic = pcall(function()
      micRec = SpeechRecognizer.createSpeechRecognizer(activity)
      local it = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH)
      it.putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
      it.putExtra(RecognizerIntent.EXTRA_LANGUAGE, "hi-IN")
      it.putExtra(RecognizerIntent.EXTRA_PARTIAL_RESULTS, false)
      local done = false
      micRec.setRecognitionListener(RecognitionListener{
        onReadyForSpeech = function() if not done then micBtn.setText("Listening...") end end,
        onBeginningOfSpeech = function() end,
        onRmsChanged = function() end,
        onBufferReceived = function() end,
        onEndOfSpeech = function() micBtn.setText("Microphone") end,
        onError = function()
          if done then return end
          done = true
          isMicBusy = false
          micBtn.setText("Microphone")
          pcall(function() if micRec then micRec.cancel() micRec.destroy() micRec = nil end end)
        end,
        onResults = function(res)
          if done then return end
          done = true
          isMicBusy = false
          micBtn.setText("Microphone")
          local matches = res.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
          pcall(function() if micRec then micRec.cancel() micRec.destroy() micRec = nil end end)
          if matches and matches.size() > 0 then
            runAssistantQuery(tostring(matches.get(0)))
          end
        end,
        onPartialResults = function() end,
        onEvent = function() end
      })
      micRec.startListening(it)
    end)
    if not okMic then
      isMicBusy = false
      micBtn.setText("Microphone")
      showToast("Microphone unavailable.")
    end
  end)

  moreBtn.setOnClickListener(function()
    local curM = ast_models[model_idx] or ast_models[1]
    local opts = {
      "Open BTP Live Voice Mode",
      "Personal Chat Assistant Setup & Train",
      "Change Model (" .. curM.displayName .. ")",
      "Auto TTS: " .. (auto_tts and "ON" or "OFF"),
      "Memory: " .. (mem_enabled and "ON" or "OFF"),
      "Send Feedback to Assistant",
      "Clear Assistant Memory",
      "About BTP Assistant"
    }
    AlertDialog.Builder(activity)
      .setTitle("Assistant Options")
      .setItems(opts, DialogInterface.OnClickListener{
        onClick = function(_, w)
          if w == 0 then
            stopAstAudio()
            openAssistantLiveVoiceDialog()
          elseif w == 1 then
            showPersonalAssistantSetupDialog()
          elseif w == 2 then
            local names = {}
            for _, m in ipairs(ast_models) do table.insert(names, m.displayName) end
            AlertDialog.Builder(activity)
              .setTitle("Select AI Model")
              .setItems(names, DialogInterface.OnClickListener{
                onClick = function(_, mIdx)
                  model_idx = mIdx + 1
                  sp.edit().putInt("btp_ast_model_idx", model_idx).apply()
                  showToast("Model: " .. ast_models[model_idx].displayName)
                end
              }).show()
          elseif w == 3 then
            auto_tts = not auto_tts
            sp.edit().putBoolean("btp_ast_auto_tts", auto_tts).apply()
            showToast("Auto TTS: " .. (auto_tts and "ON" or "OFF"))
          elseif w == 4 then
            mem_enabled = not mem_enabled
            sp.edit().putBoolean("btp_ast_mem_on", mem_enabled).apply()
            showToast("Memory: " .. (mem_enabled and "ON" or "OFF"))
          elseif w == 5 then
            awaitingFeedbackInput = true
            appendAstBubble("BTP Assistant", "Apna feedback type karein aur Send dabayein.", true, false)
          elseif w == 6 then
            chatHistory = {}
            sp.edit().putString("btp_ast_memory", "").apply()
            showToast("Assistant memory cleared.")
          elseif w == 7 then
            showMessage("About BTP Assistant", "Name: BTP Assistant\nPlatform: " .. APP_TITLE .. "\nDeveloper: " .. APP_DEV .. "\nModel: " .. curM.displayName)
          end
        end
      }).show()
  end)

  local dlg = AlertDialog.Builder(activity)
    .setTitle("BTP Assistant")
    .setView(root)
    .setNegativeButton("Close", DialogInterface.OnClickListener{
      onClick = function()
        isGenerating = false
        isMicBusy = false
        stopAstAudio()
        pcall(function() if micRec then micRec.cancel() micRec.destroy() micRec = nil end end)
      end
    })
    .create()

  dlg.setOnDismissListener(DialogInterface.OnDismissListener{
    onDismiss = function()
      isGenerating = false
      isMicBusy = false
      stopAstAudio()
      pcall(function() if micRec then micRec.cancel() micRec.destroy() micRec = nil end end)
    end
  })

  dlg.show()
end

-- ========================================================
-- ASSISTANT MANAGEMENT DIALOG (ADMIN / VERIFIED)
-- ========================================================

local function showAssistantManagementDialog()
  if not isVerifiedUser(current_username) then
    showToast("Only verified users can access Assistant Management.")
    return
  end

  local layout = makeLayout(true, 14)
  local lockBtn = makeButton(assistant_is_locked and "Unlock BTP Assistant (Currently Locked)" or "Lock BTP Assistant (Hide Input for Users)")
  local trainBtn = makeButton("Train Global Assistant (Add / View Q&A Knowledge)")
  local fbBtn = makeButton("View User Feedbacks from Assistant")

  layout.addView(lockBtn)
  layout.addView(trainBtn)
  layout.addView(fbBtn)

  lockBtn.setOnClickListener(function()
    local nextLock = not assistant_is_locked
    http_post_or_put(FIREBASE_URL .. "settings/assistant_locked.json", "PUT", nextLock, function(ok)
      if ok then
        assistant_is_locked = nextLock
        lockBtn.setText(assistant_is_locked and "Unlock BTP Assistant (Currently Locked)" or "Lock BTP Assistant (Hide Input for Users)")
        showToast(assistant_is_locked and "Assistant locked." or "Assistant unlocked.")
      end
    end)
  end)

  trainBtn.setOnClickListener(function()
    local tBox = makeLayout(true, 12)
    local qInp = EditText(activity)
    qInp.setHint("Question / Topic / Keyword")
    local aInp = EditText(activity)
    aInp.setHint("Trained Answer / Information")
    aInp.setMinLines(3)
    tBox.addView(qInp)
    tBox.addView(aInp)

    local existingStr = ""
    for i, it in ipairs(assistant_trained_items) do
      existingStr = existingStr .. tostring(i) .. ". Q: " .. tostring(it.q or "") .. "\n    A: " .. tostring(it.a or "") .. "\n\n"
    end
    local listTv = makeText(existingStr ~= "" and existingStr or "No trained items yet.", 12)
    local sc = ScrollView(activity)
    sc.addView(listTv)
    tBox.addView(sc, LinearLayout.LayoutParams(-1, 220))

    AlertDialog.Builder(activity)
      .setTitle("Train Global BTP Assistant")
      .setView(tBox)
      .setPositiveButton("Save Training", DialogInterface.OnClickListener{
        onClick = function()
          local qT = trim(qInp.getText())
          local aT = trim(aInp.getText())
          if qT == "" or aT == "" then
            showToast("Please enter both question and answer.")
            return
          end
          table.insert(assistant_trained_items, { q = qT, a = aT, added_by = current_username })
          http_post_or_put(FIREBASE_URL .. "settings/assistant_training.json", "PUT", assistant_trained_items, function(ok)
            if ok then showToast("Assistant trained with new knowledge!") end
          end)
        end
      })
      .setNegativeButton("Close", nil)
      .show()
  end)

  fbBtn.setOnClickListener(function()
    http_get(FIREBASE_URL .. "settings/assistant_feedbacks.json", function(s, r)
      local lines = {}
      if s and r and r ~= "null" then
        local ok, data = pcall(cjson.decode, r)
        if ok and type(data) == "table" then
          for _, item in pairs(data) do
            if type(item) == "table" then
              table.insert(lines, tostring(item.user or "User") .. " (" .. tostring(item.timestamp or "") .. "):\n" .. tostring(item.message or ""))
            end
          end
        end
      end
      showMessage("Assistant User Feedbacks", #lines > 0 and table.concat(lines, "\n\n") or "No feedback received yet.")
    end)
  end)

  AlertDialog.Builder(activity)
    .setTitle("Assistant Management")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .show()
end

-- ========================================================
-- DATA-SAVING CLEANUP & ANNOUNCEMENT / YOUTUBE LINK CHECKER
-- ========================================================

local function runSilentAutoCleanup()
  if not isNetworkAvailable() or not isAppForeground then return end
  local now = os.time()
  local last_cleanup = tonumber(sp.getString("last_cleanup_epoch", "0")) or 0
  if (now - last_cleanup) < 86400 then
    return
  end
  sp.edit().putString("last_cleanup_epoch", tostring(now)).apply()

  pcall(function()
    local seven_days_sec = 7 * 86400
    local three_days_sec = 3 * 86400

    http_get(FIREBASE_URL .. "btp_groups.json", function(s, r)
      if s and r and r ~= "null" then
        local ok, groups = pcall(cjson.decode, r)
        if ok and type(groups) == "table" then
          for gid, g in pairs(groups) do
            if type(g) == "table" and not g.is_banned then
              local last_act = tonumber(g.last_activity_epoch or g.created_epoch or 0)
              local mem_count = g.members and table_size(g.members) or 1
              if last_act > 0 and (now - last_act) >= three_days_sec and mem_count < 5 then
                http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. ".json", function() end)
                http_delete(FIREBASE_URL .. "btp_group_messages/" .. gid .. ".json", function() end)
              end
            end
          end
        end
      end
    end)

    http_get(FIREBASE_URL .. "unblock_requests.json", function(s, r)
      if s and r and r ~= "null" then
        local ok, data = pcall(cjson.decode, r)
        if ok and type(data) == "table" then
          for u, req in pairs(data) do
            if type(req) == "table" and req.timestamp_epoch and (now - tonumber(req.timestamp_epoch)) > seven_days_sec then
              http_delete(FIREBASE_URL .. "unblock_requests/" .. u .. ".json", function() end)
            end
          end
        end
      end
    end)
  end)
end

local function checkYoutubeBroadcastDialog()
  if not isNetworkAvailable() then return end
  http_get(FIREBASE_URL .. "settings/youtube_broadcast.json", function(s, r)
    if s and r and r ~= "null" then
      local ok, data = pcall(cjson.decode, r)
      if ok and type(data) == "table" then
        local yt_id = tostring(data.yt_id or "")
        local yt_title = trim(tostring(data.title or ""))
        local yt_url = trim(tostring(data.url or ""))
        if yt_id ~= "" and yt_url ~= "" then
          local seen_yt = tostring(sp.getString("last_seen_yt_broadcast_id", ""))
          if seen_yt == yt_id then return end

          playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP2, false)
          local box = makeLayout(true, 16)
          box.addView(makeText(yt_title ~= "" and yt_title or "New Video Shared by Admin", 16))
          box.addView(makeText("Tap 'Play on YouTube' to watch directly on YouTube.", 13))

          AlertDialog.Builder(activity)
            .setTitle("YouTube Video Broadcast")
            .setView(box)
            .setCancelable(false)
            .setPositiveButton("Play on YouTube", DialogInterface.OnClickListener{
              onClick = function()
                sp.edit().putString("last_seen_yt_broadcast_id", yt_id).apply()
                pcall(function()
                  local intent = Intent(Intent.ACTION_VIEW, Uri.parse(yt_url))
                  activity.startActivity(intent)
                end)
              end
            })
            .setNegativeButton("Close", DialogInterface.OnClickListener{
              onClick = function()
                sp.edit().putString("last_seen_yt_broadcast_id", yt_id).apply()
              end
            })
            .show()
        end
      end
    end
  end)
end

local function checkPopupAnnouncementNote()
  if not isNetworkAvailable() then
    return
  end
  http_get(FIREBASE_URL .. "settings/popup_announcement.json", function(s, r)
    if s and r and r ~= "null" then
      local ok, data = pcall(cjson.decode, r)
      local note_text = ""
      local note_time = ""
      local note_id = ""
      if ok and type(data) == "table" then
        note_text = trim(tostring(data.message or ""))
        note_time = tostring(data.timestamp or "")
        note_id = tostring(data.note_id or note_time or note_text)
      elseif ok and type(data) == "string" then
        note_text = trim(data)
        note_id = note_text
      end

      if note_text ~= "" then
        local last_seen_note_id = tostring(sp.getString("last_seen_announcement_id", ""))
        if last_seen_note_id == note_id then
          checkYoutubeBroadcastDialog()
          return
        end

        playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP2, false)
        local display_msg = note_text
        if note_time ~= "" then
          display_msg = display_msg .. "\n\nPosted: " .. note_time
        end
        AlertDialog.Builder(activity)
          .setTitle("Announcement Note")
          .setMessage(display_msg)
          .setCancelable(false)
          .setPositiveButton("OK", DialogInterface.OnClickListener{
            onClick = function()
              sp.edit().putString("last_seen_announcement_id", note_id).apply()
              checkYoutubeBroadcastDialog()
            end
          })
          .show()
      else
        checkYoutubeBroadcastDialog()
      end
    else
      checkYoutubeBroadcastDialog()
    end
  end)
end

-- ========================================================
-- CHECK GLOBAL ADMIN BLOCK STATUS
-- ========================================================

local function checkBlockStatus(onNotBlocked)
  if current_username == "" or isDeveloper(current_username) or not isNetworkAvailable() then
    if onNotBlocked then onNotBlocked() end
    return
  end

  http_get(FIREBASE_URL .. "blocked/" .. encodeKey(current_username) .. ".json", function(success, response)
    if success and response and (response == "true" or response == '"true"') then
      local layout = makeLayout(true, 20)
      layout.addView(makeText("Access Denied!\nYou have been blocked by the admin due to policy violations.", 15))
      
      local req_btn = makeButton("Send Unblock Request")
      layout.addView(req_btn)

      local dialog = AlertDialog.Builder(activity)
        .setTitle("Notice: You Are Blocked")
        .setView(layout)
        .setCancelable(false)
        .setPositiveButton("Exit Application", DialogInterface.OnClickListener{
          onClick = function()
            activity.finish()
          end
        })
        .create()

      dialog.show()

      req_btn.setOnClickListener(function()
        local unblock_req = {
          user = current_username,
          message = "Please unblock my account.",
          timestamp = os.date("%I:%M %p, %d %b"),
          timestamp_epoch = os.time()
        }
        http_post_or_put(FIREBASE_URL .. "unblock_requests/" .. encodeKey(current_username) .. ".json", "PUT", unblock_req, function(ok)
          showToast("Unblock request submitted successfully to admin.")
        end)
      end)
    else
      if onNotBlocked then onNotBlocked() end
    end
  end)
end

-- ========================================================
-- WELCOME / LOGIN
-- ========================================================

function showWelcomeDialog()
  local layout = makeLayout(true, 30)

  local message = makeText(
    "WELCOME TO\n" .. APP_TITLE .. "!\n\n"
    .. APP_DEV .. "\n\n"
    .. "Disclaimer & Terms:\n"
    .. "All source codes shared on this platform are public.\n\n"
    .. "Share open-source Lua code responsibly.\n"
    .. "Created & Copyright by Ibrahim Ansari",
    14
  )
  layout.addView(message)

  local input = EditText(activity)
  input.setHint("Enter Your Name (Required)")
  layout.addView(input)

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Welcome")
    .setView(layout)
    .setCancelable(false)
    .setPositiveButton("Login / Continue", nil)
    .create()

  dialog.show()

  dialog.getButton(-1).setOnClickListener(View.OnClickListener{
    onClick = function()
      local name = trim(input.getText())
      if name == "" then
        showToast("Please enter your name to proceed!")
        return
      end

      sp.edit().putString("username", name).apply()
      current_username = name
      registerUserToFirebase(name)
      startPresenceTracking()
      startIncomingCallWatcher()
      dialog.dismiss()
      initMainWindow()
      checkPopupAnnouncementNote()
      Handler(Looper.getMainLooper()).postDelayed(Runnable({
        run = function()
          checkUpdate(false)
        end
      }), 2000)
    end
  })
end

local function copyCode(code)
  local clipboard = activity.getSystemService(Context.CLIPBOARD_SERVICE)
  clipboard.setText(tostring(code or ""))
  showToast("Code copied to clipboard!")
end

-- ========================================================
-- NOTIFICATIONS & LIKE SOUND WATCHER
-- ========================================================

function stopBackgroundNotificationWatcher()
  if bg_notif_handler ~= nil and bg_notif_runnable ~= nil then
    pcall(function()
      bg_notif_handler.removeCallbacks(bg_notif_runnable)
    end)
    bg_notif_handler = nil
    bg_notif_runnable = nil
  end
end

function updateNotificationCount(silent)
  if not notif_button or not isNetworkAvailable() or not isAppForeground then return end
  
  local seen_map = getSeenNotifsMap()

  http_get(FIREBASE_URL .. "codes.json", function(success, response)
    if not success or not response or response == "null" or not isAppForeground then return end

    local unseen_notif_count = 0
    local new_code_discovered = false
    local new_like_discovered = false
    local new_comment_discovered = false

    local ok, data = pcall(cjson.decode, response)
    if ok and type(data) == "table" then
      for k, v in pairs(data) do
        if type(v) == "table" then
          if is_first_bg_sync_done and not known_code_ids[k] then
            new_code_discovered = true
          end
          known_code_ids[k] = true

          if trim(tostring(v.author or "")):lower() == trim(current_username):lower() then
            if v.likes then
              for liker, _ in pairs(v.likes) do
                local dec_liker = Uri.decode(tostring(liker))
                if trim(dec_liker):lower() ~= trim(current_username):lower() then
                  local l_key = "like_" .. k .. "_" .. dec_liker
                  if not seen_map[l_key] then
                    unseen_notif_count = unseen_notif_count + 1
                  end
                  if is_first_bg_sync_done and not known_notif_keys[l_key] then
                    new_like_discovered = true
                  end
                  known_notif_keys[l_key] = true
                end
              end
            end
            if v.comments then
              for cid, c in pairs(v.comments) do
                if c.user and trim(tostring(c.user)):lower() ~= trim(current_username):lower() then
                  local c_key = "com_" .. k .. "_" .. tostring(cid)
                  if not seen_map[c_key] then
                    unseen_notif_count = unseen_notif_count + 1
                  end
                  if is_first_bg_sync_done and not known_notif_keys[c_key] then
                    new_comment_discovered = true
                  end
                  known_notif_keys[c_key] = true
                end
              end
            end
          end
        end
      end
    end

    http_get(FIREBASE_URL .. "settings/broadcast.json", function(s_b, r_b)
      if not isAppForeground then return end
      if s_b and r_b and r_b ~= "null" then
        local b_text = tostring(r_b)
        local ok_b, dec_b = pcall(cjson.decode, r_b)
        if ok_b and type(dec_b) == "string" then b_text = dec_b end
        local b_key = "broadcast_" .. b_text
        if not seen_map[b_key] then
          unseen_notif_count = unseen_notif_count + 1
        end
        if is_first_bg_sync_done and not known_notif_keys[b_key] then
          new_comment_discovered = true
        end
        known_notif_keys[b_key] = true
      end

      local count_str = unseen_notif_count > 99 and "99+" or tostring(unseen_notif_count)
      notif_button.setText("Notifications (" .. count_str .. ")")

      if chat_tab_btn then
        chat_tab_btn.setText("Chat")
      end

      if is_first_bg_sync_done and new_like_discovered then
        playSound(SOUND_LIKE, nil, ToneGenerator.TONE_PROP_ACK, false)
      end

      local sound_allowed = sp.getBoolean("notif_sound_enabled", false)
      if not silent and sound_allowed and is_first_bg_sync_done then
        if new_code_discovered or new_comment_discovered then
          playNotificationSoundDebounced()
        end
      end

      is_first_bg_sync_done = true
    end)
  end)
end

local function startBackgroundNotificationWatcher()
  if not sp.getBoolean("notif_sound_enabled", false) or not isAppForeground then return end
  if bg_notif_handler == nil then
    bg_notif_handler = Handler(Looper.getMainLooper())
    bg_notif_runnable = Runnable({
      run = function()
        if isAppForeground and isNetworkAvailable() and sp.getBoolean("notif_sound_enabled", false) then
          updateNotificationCount(false)
          if bg_notif_handler and bg_notif_runnable then
            bg_notif_handler.postDelayed(bg_notif_runnable, 60000)
          end
        else
          stopBackgroundNotificationWatcher()
        end
      end
    })
    bg_notif_handler.postDelayed(bg_notif_runnable, 60000)
  end
end

function showNotificationsDialog()
  local layout = makeLayout(true, 15)
  local scroll = ScrollView(activity)
  local container = makeLayout(true, 10)
  scroll.addView(container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 600))

  container.addView(makeText("Loading notifications...", 14))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Notifications")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()

  dialog.show()

  http_get(FIREBASE_URL .. "codes.json", function(success, response)
    container.removeAllViews()
    local notifs = {}
    local seen_map = getSeenNotifsMap()

    http_get(FIREBASE_URL .. "settings/broadcast.json", function(s_b, r_b)
      if s_b and r_b and r_b ~= "null" then
        local b_text = tostring(r_b)
        local ok_b, dec_b = pcall(cjson.decode, r_b)
        if ok_b and type(dec_b) == "string" then b_text = dec_b end
        local b_key = "broadcast_" .. b_text
        seen_map[b_key] = true
        table.insert(notifs, {
          text = "Announcement: " .. b_text,
          time = "Admin Broadcast"
        })
      end

      if success and response and response ~= "null" then
        local ok, data = pcall(cjson.decode, response)
        if ok and type(data) == "table" then
          for k, v in pairs(data) do
            if type(v) == "table" and trim(tostring(v.author or "")):lower() == trim(current_username):lower() then
              if v.likes then
                for liker, _ in pairs(v.likes) do
                  local decoded_liker = Uri.decode(tostring(liker))
                  if trim(decoded_liker):lower() ~= trim(current_username):lower() then
                    local l_key = "like_" .. k .. "_" .. decoded_liker
                    seen_map[l_key] = true
                    table.insert(notifs, {
                      text = decoded_liker .. " liked your code: " .. (v.title or "Untitled"),
                      time = v.timestamp or ""
                    })
                  end
                end
              end
              if v.comments then
                for cid, c in pairs(v.comments) do
                  if c.user and trim(tostring(c.user)):lower() ~= trim(current_username):lower() then
                    local c_key = "com_" .. k .. "_" .. tostring(cid)
                    seen_map[c_key] = true
                    table.insert(notifs, {
                      text = c.user .. " commented on \"" .. (v.title or "Untitled") .. "\": " .. (c.text or ""),
                      time = c.timestamp or ""
                    })
                  end
                end
              end
            end
          end
        end
      end

      saveSeenNotifsMap(seen_map)

      local total_count = #notifs
      dialog.setTitle("Notifications (" .. tostring(total_count) .. ")")

      if total_count == 0 then
        container.addView(makeText("No notifications.", 15))
      else
        for _, n in ipairs(notifs) do
          local card = makeLayout(true, 8)
          card.setBackgroundColor(0xFFEEEEEE)
          card.addView(makeText(n.text, 14))
          card.addView(makeText(n.time, 11))
          container.addView(card, LinearLayout.LayoutParams(-1, -2))
        end
      end
      updateNotificationCount(true)
    end)
  end)
end

-- ========================================================
-- PERSONAL CHAT (1-ON-1 WITH OFFLINE CACHE & BTP ASSISTANT AUTO-REPLY)
-- ========================================================

local function getSymmetricChatKey(u1, u2)
  local s1 = trim(tostring(u1 or "")):lower()
  local s2 = trim(tostring(u2 or "")):lower()
  if s1 < s2 then
    return encodeKey(s1) .. "_" .. encodeKey(s2)
  else
    return encodeKey(s2) .. "_" .. encodeKey(s1)
  end
end

function openPersonalChat(target_user)
  local layout = makeLayout(true, 10)

  local chat_header = makeLayout(false, 5)
  local initial_status_label = isNetworkAvailable() and " (Checking...)" or " (Offline)"
  local chat_title_tv = makeText(getVerifiedName(target_user) .. initial_status_label, 15)
  chat_title_tv.setTextColor(0xFF1E88E5)
  chat_header.addView(chat_title_tv, LinearLayout.LayoutParams(0, -2, 1))

  local more_btn = makeButton("More Options")
  chat_header.addView(more_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(chat_header)

  local managed_by_ast_banner = makeText("This chat is managed by BTP Assistant when user is offline.", 12)
  managed_by_ast_banner.setBackgroundColor(0xFFEDE7F6)
  managed_by_ast_banner.setTextColor(0xFF4A148C)
  managed_by_ast_banner.setPadding(8, 6, 8, 6)
  managed_by_ast_banner.setVisibility(View.GONE)
  layout.addView(managed_by_ast_banner)

  local block_notice_banner = makeText("", 13)
  block_notice_banner.setTextColor(0xFFD32F2F)
  block_notice_banner.setPadding(6, 6, 6, 6)
  block_notice_banner.setVisibility(View.GONE)
  layout.addView(block_notice_banner)

  local scroll = ScrollView(activity)
  local chat_container = makeLayout(true, 8)
  scroll.addView(chat_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 310))

  local reply_banner = makeLayout(false, 8)
  reply_banner.setBackgroundColor(0xFFE0E0E0)
  reply_banner.setVisibility(View.GONE)

  local reply_text_preview = makeText("", 12)
  reply_text_preview.setTextColor(0xFF333333)
  reply_banner.addView(reply_text_preview, LinearLayout.LayoutParams(0, -2, 1))

  local cancel_reply_btn = makeButton("Cancel Reply")
  reply_banner.addView(cancel_reply_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(reply_banner)

  local active_reply_target = nil

  cancel_reply_btn.setOnClickListener(function()
    active_reply_target = nil
    reply_banner.setVisibility(View.GONE)
  end)

  local input_layout = makeLayout(false, 4)
  local msg_input = EditText(activity)
  msg_input.setHint("Type a message...")
  input_layout.addView(msg_input, LinearLayout.LayoutParams(0, -2, 1))

  local send_btn = makeButton("Send")
  input_layout.addView(send_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(input_layout)

  local voice_section = makeLayout(true, 6)
  voice_section.setBackgroundColor(0xFFECEFF1)

  local voice_status_tv = makeText("", 12)
  voice_status_tv.setTextColor(0xFF37474F)
  voice_status_tv.setVisibility(View.GONE)
  voice_section.addView(voice_status_tv)

  local voice_main_btn = makeButton("Record Voice Message")
  voice_section.addView(voice_main_btn, LinearLayout.LayoutParams(-1, -2))

  local voice_call_btn = makeButton("Live Voice Call")
  voice_section.addView(voice_call_btn, LinearLayout.LayoutParams(-1, -2))

  local voice_action_row = makeLayout(false, 2)
  voice_action_row.setVisibility(View.GONE)
  local voice_preview_btn = makeButton("Preview")
  local voice_send_preview_btn = makeButton("Send Voice")
  local voice_discard_btn = makeButton("Discard")

  voice_action_row.addView(voice_preview_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_action_row.addView(voice_send_preview_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_action_row.addView(voice_discard_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_section.addView(voice_action_row)

  layout.addView(voice_section)

  local go_back_btn = makeButton("Go Back")
  layout.addView(go_back_btn, LinearLayout.LayoutParams(-1, -2))

  local dialog = AlertDialog.Builder(activity)
    .setTitle(getVerifiedName(target_user) .. initial_status_label)
    .setView(layout)
    .setCancelable(true)
    .create()

  dialog.show()

  local room_key = getSymmetricChatKey(current_username, target_user)
  local cache_key_pchat = "pchat_cache_" .. room_key
  local seen_message_ids = {}
  local is_chat_active = true
  local is_initial_load = true
  local chat_open_time = os.date("%Y%m%d%H%M%S")
  local last_rendered_data_hash = ""
  local live_handler = Handler(Looper.getMainLooper())
  local live_runnable = nil

  local is_blocked_by_them = false
  local is_blocked_by_me = false
  local target_is_currently_online = false
  local target_personal_ast_cfg = nil

  local voice_state = "idle"
  local media_recorder = nil
  local preview_player = nil
  local recorded_file_path = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_voice_rec.m4a"
  local record_seconds = 0
  local record_timer_handler = Handler(Looper.getMainLooper())
  local record_timer_runnable = nil

  local function stopPreviewPlayer()
    if preview_player ~= nil then
      pcall(function()
        if preview_player.isPlaying() then preview_player.stop() end
        preview_player.release()
      end)
      preview_player = nil
    end
    voice_preview_btn.setText("Preview")
  end

  local function resetVoiceUI()
    voice_state = "idle"
    record_seconds = 0
    if record_timer_runnable then
      pcall(function() record_timer_handler.removeCallbacks(record_timer_runnable) end)
      record_timer_runnable = nil
    end
    if media_recorder ~= nil then
      pcall(function()
        media_recorder.stop()
        media_recorder.release()
      end)
      media_recorder = nil
    end
    stopPreviewPlayer()
    voice_main_btn.setText("Record Voice Message")
    voice_main_btn.setVisibility(View.VISIBLE)
    voice_action_row.setVisibility(View.GONE)
    voice_status_tv.setVisibility(View.GONE)
    voice_status_tv.setText("")
  end

  local function stopChatPolling()
    is_chat_active = false
    resetVoiceUI()
    stopActiveVoicePlayer(false)
    current_voice_playlist = {}
    if live_handler and live_runnable then
      pcall(function() live_handler.removeCallbacks(live_runnable) end)
      live_runnable = nil
    end
    updateNotificationCount(true)
  end

  go_back_btn.setOnClickListener(function()
    stopChatPolling()
    dialog.dismiss()
  end)

  dialog.setOnDismissListener(DialogInterface.OnDismissListener{ onDismiss = stopChatPolling })
  dialog.setOnCancelListener(DialogInterface.OnCancelListener{ onCancel = stopChatPolling })

  voice_call_btn.setOnClickListener(function()
    if is_blocked_by_them or is_blocked_by_me then
      showToast("Cannot place voice call while blocked.")
      return
    end
    initiateVoiceCall("direct", target_user, getVerifiedName(target_user), {target_user})
  end)

  local function checkTargetPersonalAssistantConfig()
    if not is_chat_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "personal_assistants/" .. encodeKey(target_user) .. ".json", function(s, r)
      if not is_chat_active then return end
      if s and r and r ~= "null" then
        local ok, cfg = pcall(cjson.decode, r)
        if ok and type(cfg) == "table" and (cfg.enabled == true or cfg.enabled == "true") then
          target_personal_ast_cfg = cfg
          managed_by_ast_banner.setText("This chat is managed by BTP Assistant when " .. target_user .. " is offline.")
          managed_by_ast_banner.setVisibility(View.VISIBLE)
          return
        end
      end
      target_personal_ast_cfg = nil
      managed_by_ast_banner.setVisibility(View.GONE)
    end)
  end

  local function renderPersonalMessagesFromRaw(raw_json_str, force_refresh, from_network)
    local msg_list = {}
    local current_hash_builder = {}

    if raw_json_str and raw_json_str ~= "null" then
      local ok, data = pcall(cjson.decode, raw_json_str)
      if ok and type(data) == "table" then
        for k, v in pairs(data) do
          if type(v) == "table" then
            v.id = k
            table.insert(msg_list, v)
            if from_network then
              local base_msg_url = FIREBASE_URL .. "personal_chats/" .. room_key .. "/" .. k
              if trim(tostring(v.receiver or "")):lower() == trim(current_username):lower() then
                markMessageSeenInFirebase(base_msg_url)
                if v.status ~= "Read" then
                  v.status = "Read"
                  http_post_or_put(base_msg_url .. "/status.json", "PUT", "Read", function() end)
                end
              end
            end
          end
        end
      end
    end

    table.sort(msg_list, function(a, b)
      return tostring(a.timestamp_raw or a.timestamp or "") < tostring(b.timestamp_raw or b.timestamp or "")
    end)

    local new_reaction_on_my_msg = false
    for _, m in ipairs(msg_list) do
      local r_pairs = {}
      if type(m.reactions) == "table" then
        for rk, rv in pairs(m.reactions) do
          table.insert(r_pairs, tostring(rk) .. "=" .. tostring(rv))
          local rx_unique = "p_" .. tostring(m.id) .. "_" .. tostring(rk) .. "_" .. tostring(rv)
          if trim(tostring(m.sender or "")):lower() == trim(current_username):lower() and trim(Uri.decode(tostring(rk))):lower() ~= trim(current_username):lower() then
            if not is_initial_load and not known_reaction_keys[rx_unique] then
              new_reaction_on_my_msg = true
            end
          end
          known_reaction_keys[rx_unique] = true
        end
      end
      table.sort(r_pairs)
      local seen_cnt = (type(m.seen_by) == "table") and table_size(m.seen_by) or 0
      local played_cnt = (type(m.played_by) == "table") and table_size(m.played_by) or 0
      local del_flag = (m.deleted_for_everyone == true or m.deleted_for_everyone == "true") and "1" or "0"
      table.insert(current_hash_builder, tostring(m.id) .. ":" .. tostring(m.status or "") .. ":" .. del_flag .. ":" .. tostring(seen_cnt) .. ":" .. tostring(played_cnt) .. ":" .. table.concat(r_pairs, ","))
    end
    local current_data_hash = table.concat(current_hash_builder, "|")

    if new_reaction_on_my_msg and is_chat_active and from_network then
      playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
    end

    if current_data_hash == last_rendered_data_hash and not is_initial_load and not force_refresh then
      return
    end

    if active_voice_player ~= nil and not force_refresh then
      return
    end

    local new_incoming_msg = false
    for _, m in ipairs(msg_list) do
      if not seen_message_ids[m.id] then
        seen_message_ids[m.id] = true
        if from_network and not is_initial_load and trim(tostring(m.sender or "")):lower() ~= trim(current_username):lower() and tostring(m.timestamp_raw or "") > chat_open_time then
          new_incoming_msg = true
        end
      end
    end

    last_rendered_data_hash = current_data_hash
    chat_container.removeAllViews()
    local room_voice_playlist = {}

    if #msg_list == 0 then
      chat_container.addView(makeText("No messages yet. Say hello!", 14))
    else
      local last_day_header = ""
      for _, msg in ipairs(msg_list) do
        local day_lbl = getDayLabelFromRaw(msg.timestamp_raw)
        if day_lbl ~= "" and day_lbl ~= last_day_header then
          last_day_header = day_lbl
          chat_container.addView(createAccessibleDayHeader(day_lbl), LinearLayout.LayoutParams(-1, -2))
        end

        local is_me = (trim(tostring(msg.sender or "")):lower() == trim(tostring(current_username or "")):lower())
        local is_deleted_all = (msg.deleted_for_everyone == true or msg.deleted_for_everyone == "true")
        local is_ast_auto = (msg.is_assistant_auto == true or msg.is_assistant_auto == "true")
        local bubble = makeLayout(true, 8)
        if is_me then
          bubble.setBackgroundColor(0xFFDCF8C6)
        elseif is_ast_auto then
          bubble.setBackgroundColor(0xFFF3E5F5)
        else
          bubble.setBackgroundColor(0xFFFFFFFF)
        end
        bubble.setPadding(12, 10, 12, 10)

        if is_deleted_all then
          bubble.setClickable(false)
          bubble.setFocusable(true)
          local del_tv = makeText("This message was deleted", 13)
          del_tv.setTextColor(0xFF757575)
          bubble.addView(del_tv)
          chat_container.addView(bubble, LinearLayout.LayoutParams(-1, -2))
        else
          bubble.setClickable(true)
          bubble.setFocusable(true)

          if msg.reply_to and type(msg.reply_to) == "table" then
            local quote_box = makeLayout(true, 6)
            quote_box.setBackgroundColor(0xFFE8E8E8)
            quote_box.setPadding(8, 6, 8, 6)
            quote_box.addView(makeText("Replying to " .. getVerifiedName(msg.reply_to.sender) .. ":", 11))
            local q_preview = tostring(msg.reply_to.text or "")
            if #q_preview > 80 then q_preview = q_preview:sub(1, 80) .. "..." end
            local q_tv = makeText(q_preview, 12)
            q_tv.setTextColor(0xFF555555)
            quote_box.addView(q_tv)
            bubble.addView(quote_box, LinearLayout.LayoutParams(-1, -2))
          end

          local sender_label = is_me and "You" or (is_ast_auto and ("BTP Assistant (for " .. tostring(msg.sender or target_user) .. ")") or getVerifiedName(msg.sender))
          if msg.msg_type == "voice" and msg.audio_base64 then
            local dur_str = tostring(msg.audio_duration or "0") .. "s"
            local voice_title = makeText(sender_label .. ": Voice message (" .. dur_str .. ")", 14)
            voice_title.setPadding(0, 4, 0, 4)
            bubble.addView(voice_title)
            local fb_msg_url = FIREBASE_URL .. "personal_chats/" .. room_key .. "/" .. tostring(msg.id)
            buildVoiceBubblePlayer(bubble, msg, dur_str, room_voice_playlist, fb_msg_url)
          else
            local msg_content_tv = makeText(sender_label .. ": " .. (msg.text or ""), 14)
            msg_content_tv.setPadding(0, 4, 0, 4)
            bubble.addView(msg_content_tv)
          end

          renderClickableReactions(bubble, msg.reactions)

          local seen_txt = formatSeenByText(msg.seen_by)
          local meta_line = tostring(msg.timestamp or "")
          if is_me and seen_txt ~= "" then
            meta_line = meta_line .. " • " .. seen_txt
          end

          local meta_tv = makeText(meta_line, 11)
          meta_tv.setTextColor(0xFF777777)
          bubble.addView(meta_tv)

          chat_container.addView(bubble, LinearLayout.LayoutParams(-1, -2))

          bubble.setOnClickListener(View.OnClickListener{
            onClick = function()
              local opts = {"Reply", "Add Reaction", "Delete for Me", "Delete for Everyone"}
              AlertDialog.Builder(activity)
                .setTitle("Message Options")
                .setItems(opts, DialogInterface.OnClickListener{
                  onClick = function(d_sub, which)
                    local choice = opts[which + 1]
                    if choice == "Reply" then
                      active_reply_target = { sender = msg.sender, text = msg.text }
                      reply_text_preview.setText("Replying to " .. tostring(msg.sender or "") .. ":\n" .. tostring(msg.text or ""))
                      reply_banner.setVisibility(View.VISIBLE)
                      msg_input.requestFocus()
                    elseif choice == "Add Reaction" then
                      local reactions_list = {"Love", "Like", "Haha", "Fire", "Clap", "Wow"}
                      AlertDialog.Builder(activity)
                        .setTitle("Select Reaction")
                        .setItems(reactions_list, DialogInterface.OnClickListener{
                          onClick = function(d_emo, ew)
                            local selected_rx = reactions_list[ew + 1]
                            http_post_or_put(FIREBASE_URL .. "personal_chats/" .. room_key .. "/" .. msg.id .. "/reactions/" .. encodeKey(current_username) .. ".json", "PUT", selected_rx, function(rok)
                              if rok then
                                playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
                                loadMessages(true)
                              end
                            end)
                          end
                        }).show()
                    elseif choice == "Delete for Me" then
                      bubble.setVisibility(View.GONE)
                      showToast("Deleted for you.")
                    elseif choice == "Delete for Everyone" then
                      local del_url = FIREBASE_URL .. "personal_chats/" .. room_key .. "/" .. msg.id
                      http_post_or_put(del_url .. "/deleted_for_everyone.json", "PUT", true, function(ok)
                        if ok then
                          http_post_or_put(del_url .. "/text.json", "PUT", "This message was deleted", function() end)
                          http_delete(del_url .. "/audio_base64.json", function() end)
                          showToast("Deleted for everyone.")
                          loadMessages(true)
                        else
                          showToast("Failed to delete message.")
                        end
                      end)
                    end
                  end
                }).show()
            end
          })
        end
      end
    end

    current_voice_playlist = room_voice_playlist

    if is_initial_load or new_incoming_msg then
      scroll.post(Runnable({
        run = function()
          scroll.fullScroll(ScrollView.FOCUS_DOWN)
        end
      }))
    end

    if new_incoming_msg and is_chat_active and from_network then
      playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)
    end
    if from_network then
      is_initial_load = false
    end
  end

  local function loadMessages(force_refresh)
    if not is_chat_active then return end
    if is_initial_load then
      local cached_raw = loadOfflineCache(cache_key_pchat)
      if cached_raw then
        renderPersonalMessagesFromRaw(cached_raw, true, false)
      end
    end
    if not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "personal_chats/" .. room_key .. '.json?orderBy="$key"&limitToLast=80', function(success, response)
      if not is_chat_active then return end
      if success and response and response ~= "null" then
        saveOfflineCache(cache_key_pchat, response)
      end
      renderPersonalMessagesFromRaw(success and response or nil, force_refresh, true)
    end)
  end

  local function executeVoiceSendAfterPreSound(duration_sec)
    voice_status_tv.setText("Sending voice message...")
    voice_status_tv.setVisibility(View.VISIBLE)
    voice_main_btn.setEnabled(false)
    voice_send_preview_btn.setEnabled(false)

    local b64_audio = encodeFileToBase64(recorded_file_path)
    if not b64_audio or b64_audio == "" then
      showToast("Recording failed or empty audio.")
      voice_main_btn.setEnabled(true)
      voice_send_preview_btn.setEnabled(true)
      resetVoiceUI()
      return
    end

    local payload = {
      sender = current_username,
      receiver = target_user,
      msg_type = "voice",
      text = "Voice message (" .. tostring(duration_sec) .. "s)",
      audio_base64 = b64_audio,
      audio_duration = duration_sec,
      status = "Sent",
      timestamp = os.date("%I:%M %p"),
      timestamp_raw = os.date("%Y%m%d%H%M%S")
    }

    if active_reply_target ~= nil then
      payload.reply_to = active_reply_target
      active_reply_target = nil
      reply_banner.setVisibility(View.GONE)
    end

    http_post_or_put(FIREBASE_URL .. "personal_chats/" .. room_key .. ".json", "POST", payload, function(success)
      voice_main_btn.setEnabled(true)
      voice_send_preview_btn.setEnabled(true)
      resetVoiceUI()
      if success then
        playSound(SOUND_SEND, nil, ToneGenerator.TONE_PROP_BEEP, false)
        showToast("Voice message sent!")
        loadMessages(true)
      else
        showToast("Failed to send voice message.")
      end
    end)
  end

  local function sendVoicePayload(duration_sec)
    if notifyServerDownIfNeeded() then
      resetVoiceUI()
      return
    end
    playSound(SOUND_VOICE_PRE_SEND, function()
      executeVoiceSendAfterPreSound(duration_sec)
    end, ToneGenerator.TONE_PROP_PROMPT, false)
  end

  local function finishRecordingToState(target_mode)
    local final_sec = record_seconds
    if final_sec < 1 then final_sec = 1 end
    if record_timer_runnable then
      pcall(function() record_timer_handler.removeCallbacks(record_timer_runnable) end)
      record_timer_runnable = nil
    end
    if media_recorder ~= nil then
      pcall(function()
        media_recorder.stop()
        media_recorder.release()
      end)
      media_recorder = nil
    end

    if target_mode == "send" then
      sendVoicePayload(final_sec)
    else
      voice_state = "preview"
      voice_main_btn.setVisibility(View.GONE)
      voice_action_row.setVisibility(View.VISIBLE)
      voice_preview_btn.setText("Preview (" .. tostring(final_sec) .. "s)")
      voice_status_tv.setText("Recorded " .. tostring(final_sec) .. "s")
      voice_status_tv.setVisibility(View.VISIBLE)
    end
  end

  voice_main_btn.setOnClickListener(function()
    if is_blocked_by_them or is_blocked_by_me then
      showToast("Cannot send voice message while blocked.")
      return
    end
    if notifyServerDownIfNeeded() then return end

    if voice_state == "idle" then
      stopActiveVoicePlayer(false)
      local old_f = File(recorded_file_path)
      if old_f.exists() then old_f.delete() end

      media_recorder = startHighClarityRecording(recorded_file_path)
      if media_recorder == nil then
        showToast("Microphone permission required to record voice.")
        return
      end

      voice_state = "recording"
      record_seconds = 0
      voice_main_btn.setText("Stop and Send Voice")
      voice_action_row.setVisibility(View.VISIBLE)
      voice_preview_btn.setText("Stop and Preview")
      voice_send_preview_btn.setText("Send Now")
      voice_discard_btn.setText("Discard")
      voice_status_tv.setText("Recording: 0s")
      voice_status_tv.setVisibility(View.VISIBLE)

      record_timer_runnable = Runnable({
        run = function()
          if voice_state == "recording" and is_chat_active then
            record_seconds = record_seconds + 1
            voice_status_tv.setText("Recording: " .. tostring(record_seconds) .. "s")
            if record_seconds >= MAX_VOICE_SECONDS then
              finishRecordingToState("send")
            else
              record_timer_handler.postDelayed(record_timer_runnable, 1000)
            end
          end
        end
      })
      record_timer_handler.postDelayed(record_timer_runnable, 1000)

    elseif voice_state == "recording" then
      finishRecordingToState("send")
    end
  end)

  voice_preview_btn.setOnClickListener(function()
    if voice_state == "recording" then
      finishRecordingToState("preview")
      voice_send_preview_btn.setText("Send Voice")
      return
    end

    if voice_state == "preview" then
      if preview_player ~= nil then
        stopPreviewPlayer()
        return
      end
      pcall(function()
        local f = File(recorded_file_path)
        if f.exists() then
          preview_player = MediaPlayer()
          preview_player.setDataSource(recorded_file_path)
          preview_player.prepare()
          preview_player.start()
          voice_preview_btn.setText("Stop Preview")
          preview_player.setOnCompletionListener(MediaPlayer.OnCompletionListener{
            onCompletion = function()
              stopPreviewPlayer()
            end
          })
        end
      end)
    end
  end)

  voice_send_preview_btn.setOnClickListener(function()
    if voice_state == "recording" then
      finishRecordingToState("send")
    elseif voice_state == "preview" then
      stopPreviewPlayer()
      local sec = record_seconds > 0 and record_seconds or 1
      sendVoicePayload(sec)
    end
  end)

  voice_discard_btn.setOnClickListener(function()
    playSound(SOUND_DISCARD, nil, ToneGenerator.TONE_PROP_NACK, false)
    resetVoiceUI()
    showToast("Voice recording discarded.")
  end)

  local function checkPeerBlockStatus()
    if not is_chat_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "user_blocks/" .. encodeKey(target_user) .. "/" .. encodeKey(current_username) .. ".json", function(s1, r1)
      if not is_chat_active then return end
      is_blocked_by_them = (s1 and (r1 == "true" or r1 == '"true"'))

      http_get(FIREBASE_URL .. "user_blocks/" .. encodeKey(current_username) .. "/" .. encodeKey(target_user) .. ".json", function(s2, r2)
        if not is_chat_active then return end
        is_blocked_by_me = (s2 and (r2 == "true" or r2 == '"true"'))

        if is_blocked_by_them then
          block_notice_banner.setText("Notice: You have been blocked by this user. You cannot send messages.")
          block_notice_banner.setVisibility(View.VISIBLE)
          msg_input.setEnabled(false)
          send_btn.setEnabled(false)
          voice_main_btn.setEnabled(false)
          voice_call_btn.setEnabled(false)
        elseif is_blocked_by_me then
          block_notice_banner.setText("Notice: You have blocked this user. Unblock from More Options to chat.")
          block_notice_banner.setVisibility(View.VISIBLE)
          msg_input.setEnabled(false)
          send_btn.setEnabled(false)
          voice_main_btn.setEnabled(false)
          voice_call_btn.setEnabled(false)
        else
          block_notice_banner.setVisibility(View.GONE)
          msg_input.setEnabled(true)
          send_btn.setEnabled(true)
          voice_main_btn.setEnabled(true)
          voice_call_btn.setEnabled(true)
        end
      end)
    end)
  end

  local function checkTargetPresence()
    if not is_chat_active then return end
    local base_name = getVerifiedName(target_user)
    if not isNetworkAvailable() then
      target_is_currently_online = false
      chat_title_tv.setText(base_name .. " (Offline)")
      dialog.setTitle(base_name .. " (Offline)")
      return
    end
    http_get(FIREBASE_URL .. "user_presence/" .. encodeKey(target_user) .. ".json", function(s, r)
      if not is_chat_active then return end
      if s and r and r ~= "null" then
        local ok, data = pcall(cjson.decode, r)
        if ok and type(data) == "table" then
          local current_time = os.time()
          local last_time = tonumber(data.time_epoch or 0)
          if data.status == "online" and (current_time - last_time < 240) then
            target_is_currently_online = true
            chat_title_tv.setText(base_name .. " (Online)")
            dialog.setTitle(base_name .. " (Online)")
          else
            target_is_currently_online = false
            local ls = tostring(data.last_seen or "Offline")
            chat_title_tv.setText(base_name .. " (" .. ls .. ")")
            dialog.setTitle(base_name .. " (" .. ls .. ")")
          end
          return
        end
      end
      target_is_currently_online = false
      chat_title_tv.setText(base_name .. " (Offline)")
      dialog.setTitle(base_name .. " (Offline)")
    end)
  end

  checkPeerBlockStatus()
  checkTargetPresence()
  checkTargetPersonalAssistantConfig()
  loadMessages(true)

  live_runnable = Runnable({
    run = function()
      if is_chat_active and isAppForeground then
        loadMessages(false)
        checkPeerBlockStatus()
        checkTargetPresence()
        checkTargetPersonalAssistantConfig()
        live_handler.postDelayed(live_runnable, CHAT_POLL_INTERVAL_MS)
      end
    end
  })
  live_handler.postDelayed(live_runnable, CHAT_POLL_INTERVAL_MS)

  more_btn.setOnClickListener(function()
    http_get(FIREBASE_URL .. "user_blocks/" .. encodeKey(current_username) .. "/" .. encodeKey(target_user) .. ".json", function(s_blk, r_blk)
      local currently_blocked = (s_blk and (r_blk == "true" or r_blk == '"true"'))
      local block_action_title = currently_blocked and "Unblock User" or "Block User"
      local choices = {"Clear Chat", block_action_title, "My Personal BTP Assistant Settings"}

      AlertDialog.Builder(activity)
        .setTitle("More Options")
        .setItems(choices, DialogInterface.OnClickListener{
          onClick = function(d_choice, w)
            local selected = choices[w + 1]
            if selected == "Clear Chat" then
              http_delete(FIREBASE_URL .. "personal_chats/" .. room_key .. ".json", function(ok)
                if ok then
                  saveOfflineCache(cache_key_pchat, "{}")
                  showToast("Chat cleared.")
                  loadMessages(true)
                end
              end)
            elseif selected == "Block User" then
              http_post_or_put(FIREBASE_URL .. "user_blocks/" .. encodeKey(current_username) .. "/" .. encodeKey(target_user) .. ".json", "PUT", true, function(ok)
                if ok then
                  showToast("User blocked successfully.")
                  checkPeerBlockStatus()
                end
              end)
            elseif selected == "Unblock User" then
              http_delete(FIREBASE_URL .. "user_blocks/" .. encodeKey(current_username) .. "/" .. encodeKey(target_user) .. ".json", function(ok)
                if ok then
                  showToast("User unblocked successfully.")
                  checkPeerBlockStatus()
                end
              end)
            elseif selected == "My Personal BTP Assistant Settings" then
              showPersonalAssistantSetupDialog()
            end
          end
        }).show()
    end)
  end)

  local function triggerOfflineAssistantReplyIfNeeded(user_msg_text)
    if target_is_currently_online then return end
    if type(target_personal_ast_cfg) ~= "table" then return end
    if not (target_personal_ast_cfg.enabled == true or target_personal_ast_cfg.enabled == "true") then return end

    local user_train = type(target_personal_ast_cfg.training) == "table" and target_personal_ast_cfg.training or {}
    local away_prefix = trim(tostring(target_personal_ast_cfg.away_message or ""))
    local trained_ctx = buildTrainedKnowledgeContext(user_msg_text, user_train)

    local prompt = "You are BTP Assistant replying on behalf of " .. target_user .. " because " .. target_user .. " is currently offline. "
      .. (away_prefix ~= "" and ("Owner note: " .. away_prefix .. ". ") or "")
      .. (trained_ctx ~= "" and ("Owner trained info: " .. trained_ctx .. ". ") or "")
      .. "Message from " .. current_username .. ": " .. user_msg_text
      .. "\nReply politely, concisely, and naturally as BTP Assistant without emojis."

    fetchAssistantReplyWithFallback({backendId = "gemini-flash"}, prompt, user_msg_text, function(ok, ast_reply)
      local final_reply = (ok and ast_reply ~= "") and ast_reply or (away_prefix ~= "" and away_prefix or (target_user .. " is currently offline. Main BTP Assistant hoon, aapka message note kar liya gaya hai."))
      final_reply = enforceBtpAssistantIdentity(final_reply)

      local ast_payload = {
        sender = target_user,
        receiver = current_username,
        msg_type = "text",
        is_assistant_auto = true,
        text = final_reply,
        status = "Sent",
        timestamp = os.date("%I:%M %p"),
        timestamp_raw = os.date("%Y%m%d%H%M%S")
      }
      http_post_or_put(FIREBASE_URL .. "personal_chats/" .. room_key .. ".json", "POST", ast_payload, function(post_ok)
        if post_ok and is_chat_active then
          loadMessages(true)
        end
      end)
    end, user_train)
  end

  send_btn.setOnClickListener(function()
    if is_blocked_by_them then
      showToast("You cannot send messages because you are blocked by this user.")
      return
    end
    if is_blocked_by_me then
      showToast("Please unblock this user from More Options first.")
      return
    end
    if notifyServerDownIfNeeded() then return end

    local text = trim(msg_input.getText())
    if text == "" then return end

    local payload = {
      sender = current_username,
      receiver = target_user,
      msg_type = "text",
      text = text,
      status = "Sent",
      timestamp = os.date("%I:%M %p"),
      timestamp_raw = os.date("%Y%m%d%H%M%S")
    }

    if active_reply_target ~= nil then
      payload.reply_to = active_reply_target
      active_reply_target = nil
      reply_banner.setVisibility(View.GONE)
    end

    http_post_or_put(FIREBASE_URL .. "personal_chats/" .. room_key .. ".json", "POST", payload, function(success)
      if success then
        playSound(SOUND_SEND, nil, ToneGenerator.TONE_PROP_BEEP, false)
        msg_input.setText("")
        loadMessages(true)
        scroll.post(Runnable({
          run = function()
            scroll.fullScroll(ScrollView.FOCUS_DOWN)
          end
        }))
        triggerOfflineAssistantReplyIfNeeded(text)
      else
        showToast("Failed to send message.")
      end
    end)
  end)
endend
-- ========================================================
-- BTP VOICE ROOM (OFFLINE CACHE, LIVE VOICE CHAT & ONLINE FIX)
-- ========================================================

function openBtpVoiceRoomDialog()
  local layout = makeLayout(true, 10)

  local initial_lock_view = public_room_locked and not canBypassRoomLock(current_username)
  local initial_title = "BTP Voice Room"
  if not isNetworkAvailable() then
    initial_title = "BTP Voice Room (Offline)"
  elseif not initial_lock_view then
    initial_title = "BTP Voice Room (Checking online...)"
  end

  local title_tv = makeText(initial_title, 16)
  title_tv.setTextColor(0xFF1E88E5)
  title_tv.setPadding(4, 2, 4, 6)
  layout.addView(title_tv)

  local lock_banner = makeText("Only admin and developer can send message this room", 13)
  lock_banner.setTextColor(0xFFD32F2F)
  lock_banner.setPadding(6, 6, 6, 6)
  lock_banner.setVisibility(View.GONE)
  layout.addView(lock_banner)

  local scroll = ScrollView(activity)
  local chat_container = makeLayout(true, 8)
  scroll.addView(chat_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 330))

  local reply_banner = makeLayout(false, 8)
  reply_banner.setBackgroundColor(0xFFE0E0E0)
  reply_banner.setVisibility(View.GONE)

  local reply_text_preview = makeText("", 12)
  reply_text_preview.setTextColor(0xFF333333)
  reply_banner.addView(reply_text_preview, LinearLayout.LayoutParams(0, -2, 1))

  local cancel_reply_btn = makeButton("Cancel Reply")
  reply_banner.addView(cancel_reply_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(reply_banner)

  local active_reply_target = nil
  cancel_reply_btn.setOnClickListener(function()
    active_reply_target = nil
    reply_banner.setVisibility(View.GONE)
  end)

  local input_layout = makeLayout(false, 4)
  local msg_input = EditText(activity)
  msg_input.setHint("Message in BTP Voice Room...")
  input_layout.addView(msg_input, LinearLayout.LayoutParams(0, -2, 1))

  local send_btn = makeButton("Send")
  input_layout.addView(send_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(input_layout)

  local voice_section = makeLayout(true, 6)
  voice_section.setBackgroundColor(0xFFECEFF1)

  local voice_status_tv = makeText("", 12)
  voice_status_tv.setTextColor(0xFF37474F)
  voice_status_tv.setVisibility(View.GONE)
  voice_section.addView(voice_status_tv)

  local voice_main_btn = makeButton("Record Voice Message")
  voice_section.addView(voice_main_btn, LinearLayout.LayoutParams(-1, -2))

  local start_voice_chat_btn = makeButton("Start Live Voice Chat")
  start_voice_chat_btn.setContentDescription("Start Live Voice Chat")
  voice_section.addView(start_voice_chat_btn, LinearLayout.LayoutParams(-1, -2))

  local voice_action_row = makeLayout(false, 2)
  voice_action_row.setVisibility(View.GONE)
  local voice_preview_btn = makeButton("Preview")
  local voice_send_preview_btn = makeButton("Send Voice")
  local voice_discard_btn = makeButton("Discard")

  voice_action_row.addView(voice_preview_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_action_row.addView(voice_send_preview_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_action_row.addView(voice_discard_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_section.addView(voice_action_row)
  layout.addView(voice_section)

  local go_back_btn = makeButton("Go Back")
  layout.addView(go_back_btn, LinearLayout.LayoutParams(-1, -2))

  local dialog = AlertDialog.Builder(activity)
    .setTitle(initial_title)
    .setView(layout)
    .setCancelable(true)
    .create()
  dialog.show()

  local is_room_active = true
  local is_initial_load = true
  local room_open_time = os.date("%Y%m%d%H%M%S")
  local seen_ids = {}
  local last_hash = ""
  local live_handler = Handler(Looper.getMainLooper())
  local live_runnable = nil

  local voice_state = "idle"
  local media_recorder = nil
  local preview_player = nil
  local recorded_file_path = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_room_rec.m4a"
  local record_seconds = 0
  local record_timer_handler = Handler(Looper.getMainLooper())
  local record_timer_runnable = nil

  local function stopPreviewPlayer()
    if preview_player ~= nil then
      pcall(function()
        if preview_player.isPlaying() then preview_player.stop() end
        preview_player.release()
      end)
      preview_player = nil
    end
    voice_preview_btn.setText("Preview")
  end

  local function resetVoiceUI()
    voice_state = "idle"
    record_seconds = 0
    if record_timer_runnable then
      pcall(function() record_timer_handler.removeCallbacks(record_timer_runnable) end)
      record_timer_runnable = nil
    end
    if media_recorder ~= nil then
      pcall(function()
        media_recorder.stop()
        media_recorder.release()
      end)
      media_recorder = nil
    end
    stopPreviewPlayer()
    voice_main_btn.setText("Record Voice Message")
    voice_main_btn.setVisibility(View.VISIBLE)
    voice_action_row.setVisibility(View.GONE)
    voice_status_tv.setVisibility(View.GONE)
  end

  local function closeRoom()
    is_room_active = false
    resetVoiceUI()
    stopActiveVoicePlayer(false)
    current_voice_playlist = {}
    if live_handler and live_runnable then
      pcall(function() live_handler.removeCallbacks(live_runnable) end)
      live_runnable = nil
    end
  end

  go_back_btn.setOnClickListener(function()
    closeRoom()
    dialog.dismiss()
  end)

  dialog.setOnDismissListener(DialogInterface.OnDismissListener{ onDismiss = closeRoom })
  dialog.setOnCancelListener(DialogInterface.OnCancelListener{ onCancel = closeRoom })

  start_voice_chat_btn.setOnClickListener(function()
    if notifyServerDownIfNeeded() then return end
    if public_room_locked and not canBypassRoomLock(current_username) then
      showToast("Only admin and developer can send message this room")
      return
    end
    closeRoom()
    dialog.dismiss()
    initiateVoiceCall("room_live", "btp_voice_room", "BTP Voice Room Live", {})
  end)

  local function applyRoomLockAndOnlineState()
    if not is_room_active then return end
    if not isNetworkAvailable() then
      title_tv.setText("BTP Voice Room (Offline)")
      dialog.setTitle("BTP Voice Room (Offline)")
      return
    end

    local bypass_lock = canBypassRoomLock(current_username)
    local lock_enforced_for_me = (public_room_locked and not bypass_lock)

    if lock_enforced_for_me then
      lock_banner.setText("Only admin and developer can send message this room")
      lock_banner.setVisibility(View.VISIBLE)
      input_layout.setVisibility(View.GONE)
      voice_section.setVisibility(View.GONE)
      reply_banner.setVisibility(View.GONE)
      title_tv.setText("BTP Voice Room")
      dialog.setTitle("BTP Voice Room")
      return
    else
      input_layout.setVisibility(View.VISIBLE)
      voice_section.setVisibility(View.VISIBLE)
      if public_room_locked then
        lock_banner.setText("Room Locked for Members (Only admin and developer can send message this room)")
        lock_banner.setVisibility(View.VISIBLE)
      else
        lock_banner.setVisibility(View.GONE)
      end
    end

    http_get(FIREBASE_URL .. "user_presence.json", function(s, r)
      if not is_room_active or public_room_locked then return end
      if not isNetworkAvailable() then
        title_tv.setText("BTP Voice Room (Offline)")
        dialog.setTitle("BTP Voice Room (Offline)")
        return
      end
      local count = getOnlineUsersSummary(s and r or nil)
      local combined_title = (count > 0) and ("BTP Voice Room (" .. tostring(count) .. " online)") or "BTP Voice Room (Offline)"
      title_tv.setText(combined_title)
      dialog.setTitle(combined_title)
    end)
  end

  local function renderRoomMessagesFromRaw(raw_json_str, force_refresh, from_network)
    local msg_list = {}
    local hash_builder = {}

    if raw_json_str and raw_json_str ~= "null" then
      local ok, data = pcall(cjson.decode, raw_json_str)
      if ok and type(data) == "table" then
        for k, v in pairs(data) do
          if type(v) == "table" then
            v.id = k
            table.insert(msg_list, v)
            if from_network then
              markMessageSeenInFirebase(FIREBASE_URL .. "btp_voice_room/" .. tostring(k))
            end
          end
        end
      end
    end

    table.sort(msg_list, function(a, b)
      return tostring(a.timestamp_raw or a.timestamp or "") < tostring(b.timestamp_raw or b.timestamp or "")
    end)

    if #msg_list > 0 then
      local latest_item = msg_list[#msg_list]
      sp.edit().putString("last_seen_vr_msg_id", tostring(latest_item.id or "")).apply()
    end

    local new_rx_on_mine = false
    for _, m in ipairs(msg_list) do
      local r_pairs = {}
      if type(m.reactions) == "table" then
        for rk, rv in pairs(m.reactions) do
          table.insert(r_pairs, tostring(rk) .. "=" .. tostring(rv))
          local rx_unique = "vr_" .. tostring(m.id) .. "_" .. tostring(rk) .. "_" .. tostring(rv)
          if trim(tostring(m.sender or "")):lower() == trim(current_username):lower() and trim(Uri.decode(tostring(rk))):lower() ~= trim(current_username):lower() then
            if not is_initial_load and not known_reaction_keys[rx_unique] then
              new_rx_on_mine = true
            end
          end
          known_reaction_keys[rx_unique] = true
        end
      end
      table.sort(r_pairs)
      local seen_cnt = (type(m.seen_by) == "table") and table_size(m.seen_by) or 0
      local played_cnt = (type(m.played_by) == "table") and table_size(m.played_by) or 0
      local del_flag = (m.deleted_for_everyone == true or m.deleted_for_everyone == "true") and "1" or "0"
      table.insert(hash_builder, tostring(m.id) .. ":" .. del_flag .. ":" .. tostring(seen_cnt) .. ":" .. tostring(played_cnt) .. ":" .. table.concat(r_pairs, ","))
    end
    local cur_hash = table.concat(hash_builder, "|")

    if new_rx_on_mine and is_room_active and from_network then
      playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
    end

    if cur_hash == last_hash and not is_initial_load and not force_refresh then return end
    if active_voice_player ~= nil and not force_refresh then return end

    local new_incoming = false
    for _, m in ipairs(msg_list) do
      if not seen_ids[m.id] then
        seen_ids[m.id] = true
        if from_network and not is_initial_load and trim(tostring(m.sender or "")):lower() ~= trim(current_username):lower() and tostring(m.timestamp_raw or "") > room_open_time then
          new_incoming = true
        end
      end
    end

    last_hash = cur_hash
    chat_container.removeAllViews()
    local vr_playlist = {}

    if #msg_list == 0 then
      chat_container.addView(makeText("Welcome to BTP Voice Room. Start the conversation!", 14))
    else
      local last_day = ""
      for _, msg in ipairs(msg_list) do
        local dl = getDayLabelFromRaw(msg.timestamp_raw)
        if dl ~= "" and dl ~= last_day then
          last_day = dl
          chat_container.addView(createAccessibleDayHeader(dl), LinearLayout.LayoutParams(-1, -2))
        end

        local is_me = (trim(tostring(msg.sender or "")):lower() == trim(current_username):lower())
        local is_deleted_all = (msg.deleted_for_everyone == true or msg.deleted_for_everyone == "true")
        local bubble = makeLayout(true, 8)
        bubble.setBackgroundColor(is_me and 0xFFDCF8C6 or 0xFFFFFFFF)
        bubble.setPadding(12, 10, 12, 10)

        if is_deleted_all then
          bubble.setClickable(false)
          bubble.setFocusable(true)
          local del_tv = makeText("This message was deleted", 13)
          del_tv.setTextColor(0xFF757575)
          bubble.addView(del_tv)
          chat_container.addView(bubble, LinearLayout.LayoutParams(-1, -2))
        else
          bubble.setClickable(true)
          bubble.setFocusable(true)

          if msg.reply_to and type(msg.reply_to) == "table" then
            local qbox = makeLayout(true, 6)
            qbox.setBackgroundColor(0xFFE8E8E8)
            qbox.addView(makeText("Replying to " .. getVerifiedName(msg.reply_to.sender) .. ":", 11))
            qbox.addView(makeText(tostring(msg.reply_to.text or ""), 12))
            bubble.addView(qbox, LinearLayout.LayoutParams(-1, -2))
          end

          local sender_lbl = is_me and "You" or getVerifiedName(msg.sender)
          if msg.msg_type == "voice" and msg.audio_base64 then
            local dstr = tostring(msg.audio_duration or "0") .. "s"
            bubble.addView(makeText(sender_lbl .. ": Voice message (" .. dstr .. ")", 14))
            local fb_msg_url = FIREBASE_URL .. "btp_voice_room/" .. tostring(msg.id)
            buildVoiceBubblePlayer(bubble, msg, dstr, vr_playlist, fb_msg_url)
          else
            bubble.addView(makeText(sender_lbl .. ": " .. (msg.text or ""), 14))
          end

          renderClickableReactions(bubble, msg.reactions)

          local seen_txt = formatSeenByText(msg.seen_by)
          local meta_line = tostring(msg.timestamp or "")
          if seen_txt ~= "" then
            meta_line = meta_line .. " • " .. seen_txt
          end

          local mtv = makeText(meta_line, 11)
          mtv.setTextColor(0xFF777777)
          bubble.addView(mtv)
          chat_container.addView(bubble, LinearLayout.LayoutParams(-1, -2))

          bubble.setOnClickListener(View.OnClickListener{
            onClick = function()
              local opts = {"Add Reaction", "Delete for Me"}
              if not (public_room_locked and not canBypassRoomLock(current_username)) then
                table.insert(opts, 1, "Reply")
              end
              if not is_me and trim(tostring(msg.sender or "")) ~= "" then
                table.insert(opts, "Private Chat with " .. tostring(msg.sender))
              end
              if is_me or canBypassRoomLock(current_username) then
                table.insert(opts, "Delete for Everyone")
              end

              AlertDialog.Builder(activity)
                .setTitle("Message Options")
                .setItems(opts, DialogInterface.OnClickListener{
                  onClick = function(d_sub, which)
                    local choice = opts[which + 1]
                    if choice == "Reply" then
                      active_reply_target = { sender = msg.sender, text = msg.text }
                      reply_text_preview.setText("Replying to " .. tostring(msg.sender or "") .. ":\n" .. tostring(msg.text or ""))
                      reply_banner.setVisibility(View.VISIBLE)
                      msg_input.requestFocus()
                    elseif choice == "Add Reaction" then
                      local rlist = {"Love", "Like", "Haha", "Fire", "Clap", "Wow"}
                      AlertDialog.Builder(activity)
                        .setTitle("Select Reaction")
                        .setItems(rlist, DialogInterface.OnClickListener{
                          onClick = function(de, ew)
                            http_post_or_put(FIREBASE_URL .. "btp_voice_room/" .. msg.id .. "/reactions/" .. encodeKey(current_username) .. ".json", "PUT", rlist[ew + 1], function(ok)
                              if ok then
                                playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
                                loadRoomMessages(true)
                              end
                            end)
                          end
                        }).show()
                    elseif choice == "Delete for Me" then
                      bubble.setVisibility(View.GONE)
                      showToast("Deleted for you.")
                    elseif choice == "Delete for Everyone" then
                      local del_url = FIREBASE_URL .. "btp_voice_room/" .. msg.id
                      http_post_or_put(del_url .. "/deleted_for_everyone.json", "PUT", true, function(ok)
                        if ok then
                          http_post_or_put(del_url .. "/text.json", "PUT", "This message was deleted", function() end)
                          http_delete(del_url .. "/audio_base64.json", function() end)
                          showToast("Deleted for everyone.")
                          loadRoomMessages(true)
                        end
                      end)
                    elseif choice:find("Private Chat with ", 1, true) then
                      closeRoom()
                      dialog.dismiss()
                      openPersonalChat(msg.sender)
                    end
                  end
                }).show()
            end
          })
        end
      end
    end

    current_voice_playlist = vr_playlist

    if is_initial_load or new_incoming or force_refresh then
      scroll.post(Runnable({ run = function() scroll.fullScroll(ScrollView.FOCUS_DOWN) end }))
    end
    if new_incoming and is_room_active and from_network then
      playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)
    end
    if from_network then
      is_initial_load = false
    end
  end

  local function loadRoomMessages(force_refresh)
    if not is_room_active then return end
    if is_initial_load then
      local cached_vr = loadOfflineCache("btp_voice_room_cache")
      if cached_vr then
        renderRoomMessagesFromRaw(cached_vr, true, false)
      end
    end
    if not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. 'btp_voice_room.json?orderBy="$key"&limitToLast=80', function(success, response)
      if not is_room_active then return end
      if success and response and response ~= "null" then
        saveOfflineCache("btp_voice_room_cache", response)
      end
      renderRoomMessagesFromRaw(success and response or nil, force_refresh, true)
    end)
  end

  local function executeRoomVoiceSendAfterPreSound(duration_sec)
    voice_status_tv.setText("Sending voice message...")
    voice_status_tv.setVisibility(View.VISIBLE)
    voice_main_btn.setEnabled(false)
    voice_send_preview_btn.setEnabled(false)

    local b64_audio = encodeFileToBase64(recorded_file_path)
    if not b64_audio or b64_audio == "" then
      showToast("Recording failed or empty audio.")
      voice_main_btn.setEnabled(true)
      voice_send_preview_btn.setEnabled(true)
      resetVoiceUI()
      return
    end

    local payload = {
      sender = current_username,
      msg_type = "voice",
      text = "Voice message (" .. tostring(duration_sec) .. "s)",
      audio_base64 = b64_audio,
      audio_duration = duration_sec,
      timestamp = os.date("%I:%M %p"),
      timestamp_raw = os.date("%Y%m%d%H%M%S")
    }
    if active_reply_target ~= nil then
      payload.reply_to = active_reply_target
      active_reply_target = nil
      reply_banner.setVisibility(View.GONE)
    end

    http_post_or_put(FIREBASE_URL .. "btp_voice_room.json", "POST", payload, function(success)
      voice_main_btn.setEnabled(true)
      voice_send_preview_btn.setEnabled(true)
      resetVoiceUI()
      if success then
        playSound(SOUND_SEND, nil, ToneGenerator.TONE_PROP_BEEP, false)
        loadRoomMessages(true)
      else
        showToast("Failed to send voice message.")
      end
    end)
  end

  local function sendVoicePayload(duration_sec)
    if notifyServerDownIfNeeded() then
      resetVoiceUI()
      return
    end
    if public_room_locked and not canBypassRoomLock(current_username) then
      showToast("Only admin and developer can send message this room")
      resetVoiceUI()
      return
    end
    playSound(SOUND_VOICE_PRE_SEND, function()
      executeRoomVoiceSendAfterPreSound(duration_sec)
    end, ToneGenerator.TONE_PROP_PROMPT, false)
  end

  local function finishRecordingToState(target_mode)
    local final_sec = record_seconds
    if final_sec < 1 then final_sec = 1 end
    if record_timer_runnable then
      pcall(function() record_timer_handler.removeCallbacks(record_timer_runnable) end)
      record_timer_runnable = nil
    end
    if media_recorder ~= nil then
      pcall(function()
        media_recorder.stop()
        media_recorder.release()
      end)
      media_recorder = nil
    end
    if target_mode == "send" then
      sendVoicePayload(final_sec)
    else
      voice_state = "preview"
      voice_main_btn.setVisibility(View.GONE)
      voice_action_row.setVisibility(View.VISIBLE)
      voice_preview_btn.setText("Preview (" .. tostring(final_sec) .. "s)")
      voice_status_tv.setText("Recorded " .. tostring(final_sec) .. "s")
      voice_status_tv.setVisibility(View.VISIBLE)
    end
  end

  voice_main_btn.setOnClickListener(function()
    if notifyServerDownIfNeeded() then return end
    if public_room_locked and not canBypassRoomLock(current_username) then
      showToast("Only admin and developer can send message this room")
      return
    end

    if voice_state == "idle" then
      stopActiveVoicePlayer(false)
      local old_f = File(recorded_file_path)
      if old_f.exists() then old_f.delete() end

      media_recorder = startHighClarityRecording(recorded_file_path)
      if media_recorder == nil then
        showToast("Microphone permission required.")
        return
      end

      voice_state = "recording"
      record_seconds = 0
      voice_main_btn.setText("Stop and Send Voice")
      voice_action_row.setVisibility(View.VISIBLE)
      voice_preview_btn.setText("Stop and Preview")
      voice_send_preview_btn.setText("Send Now")
      voice_discard_btn.setText("Discard")
      voice_status_tv.setText("Recording: 0s")
      voice_status_tv.setVisibility(View.VISIBLE)

      record_timer_runnable = Runnable({
        run = function()
          if voice_state == "recording" and is_room_active then
            record_seconds = record_seconds + 1
            voice_status_tv.setText("Recording: " .. tostring(record_seconds) .. "s")
            if record_seconds >= MAX_VOICE_SECONDS then
              finishRecordingToState("send")
            else
              record_timer_handler.postDelayed(record_timer_runnable, 1000)
            end
          end
        end
      })
      record_timer_handler.postDelayed(record_timer_runnable, 1000)
    elseif voice_state == "recording" then
      finishRecordingToState("send")
    end
  end)

  voice_preview_btn.setOnClickListener(function()
    if voice_state == "recording" then
      finishRecordingToState("preview")
      voice_send_preview_btn.setText("Send Voice")
    elseif voice_state == "preview" then
      if preview_player ~= nil then
        stopPreviewPlayer()
        return
      end
      pcall(function()
        local f = File(recorded_file_path)
        if f.exists() then
          preview_player = MediaPlayer()
          preview_player.setDataSource(recorded_file_path)
          preview_player.prepare()
          preview_player.start()
          voice_preview_btn.setText("Stop Preview")
          preview_player.setOnCompletionListener(MediaPlayer.OnCompletionListener{ onCompletion = stopPreviewPlayer })
        end
      end)
    end
  end)

  voice_send_preview_btn.setOnClickListener(function()
    if voice_state == "recording" then
      finishRecordingToState("send")
    elseif voice_state == "preview" then
      stopPreviewPlayer()
      sendVoicePayload(record_seconds > 0 and record_seconds or 1)
    end
  end)

  voice_discard_btn.setOnClickListener(function()
    playSound(SOUND_DISCARD, nil, ToneGenerator.TONE_PROP_NACK, false)
    resetVoiceUI()
    showToast("Voice recording discarded.")
  end)

  applyRoomLockAndOnlineState()
  loadRoomMessages(true)

  syncServerAndRoomSettings(function()
    if is_room_active then
      applyRoomLockAndOnlineState()
      loadRoomMessages(false)
    end
  end)

  live_runnable = Runnable({
    run = function()
      if is_room_active and isAppForeground then
        applyRoomLockAndOnlineState()
        loadRoomMessages(false)
        live_handler.postDelayed(live_runnable, ROOM_POLL_INTERVAL_MS)
      end
    end
  })
  live_handler.postDelayed(live_runnable, ROOM_POLL_INTERVAL_MS)

  send_btn.setOnClickListener(function()
    if notifyServerDownIfNeeded() then return end
    if public_room_locked and not canBypassRoomLock(current_username) then
      showToast("Only admin and developer can send message this room")
      return
    end

    local text = trim(msg_input.getText())
    if text == "" then return end

    send_btn.setEnabled(false)
    local payload = {
      sender = current_username,
      msg_type = "text",
      text = text,
      timestamp = os.date("%I:%M %p"),
      timestamp_raw = os.date("%Y%m%d%H%M%S")
    }
    if active_reply_target ~= nil then
      payload.reply_to = active_reply_target
      active_reply_target = nil
      reply_banner.setVisibility(View.GONE)
    end

    http_post_or_put(FIREBASE_URL .. "btp_voice_room.json", "POST", payload, function(success)
      send_btn.setEnabled(true)
      if success then
        playSound(SOUND_SEND, nil, ToneGenerator.TONE_PROP_BEEP, false)
        msg_input.setText("")
        loadRoomMessages(true)
      else
        showToast("Failed to send message.")
      end
    end)
  end)
end

-- ========================================================
-- GROUPS SYSTEM (WITH OFFLINE CACHE & LIVE GROUP VOICE CALL)
-- ========================================================

function showCreateGroupDialog(onCreatedCallback)
  local layout = makeLayout(true, 16)

  local name_input = EditText(activity)
  name_input.setHint("Enter Group Name (Required)")
  layout.addView(name_input)

  local desc_input = EditText(activity)
  desc_input.setHint("Group Description (Up to 200 chars)")
  desc_input.setMinLines(2)
  layout.addView(desc_input)

  local approval_required = false
  local approval_toggle_btn = makeButton("Join Mode: Direct Join (No Approval)")
  layout.addView(approval_toggle_btn)

  approval_toggle_btn.setOnClickListener(function()
    approval_required = not approval_required
    if approval_required then
      approval_toggle_btn.setText("Join Mode: Approval Required")
    else
      approval_toggle_btn.setText("Join Mode: Direct Join (No Approval)")
    end
  end)

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Create New Group")
    .setView(layout)
    .setPositiveButton("Create Group", nil)
    .setNegativeButton("Cancel", nil)
    .create()
  dialog.show()

  dialog.getButton(-1).setOnClickListener(View.OnClickListener{
    onClick = function()
      if notifyServerDownIfNeeded() then return end

      local gname = trim(name_input.getText())
      if gname == "" then
        showToast("Please enter a group name.")
        return
      end
      local gdesc = trim(desc_input.getText())
      if #gdesc > 200 then gdesc = gdesc:sub(1, 200) end

      local gid = "grp_" .. tostring(os.time()) .. "_" .. tostring(math.random(100, 999))
      local members_tbl = {}
      members_tbl[encodeKey(current_username)] = current_username

      local admins_tbl = {}
      admins_tbl[encodeKey(current_username)] = true

      local group_payload = {
        id = gid,
        name = gname,
        description = gdesc,
        creator = current_username,
        approval_required = approval_required,
        send_permission = "everyone",
        is_locked = false,
        is_banned = false,
        created_epoch = os.time(),
        last_activity_epoch = os.time(),
        members = members_tbl,
        admins = admins_tbl
      }

      http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. ".json", "PUT", group_payload, function(ok)
        if ok then
          showToast("Group created successfully!")
          dialog.dismiss()
          if onCreatedCallback then onCreatedCallback() end
        else
          showToast("Failed to create group.")
        end
      end)
    end
  })
end

local function isUserGroupAdmin(group_data, uname)
  if isDeveloper(uname) then return true end
  local norm = trim(tostring(uname or "")):lower()
  if trim(tostring(group_data.creator or "")):lower() == norm then return true end
  if type(group_data.admins) == "table" then
    for k, v in pairs(group_data.admins) do
      if trim(Uri.decode(tostring(k))):lower() == norm and (v == true or v == "true") then
        return true
      end
    end
  end
  return false
end

local function isGroupCreator(group_data, uname)
  return trim(tostring(group_data.creator or "")):lower() == trim(tostring(uname or "")):lower()
end

local function isGroupLockedFlag(group_data)
  if group_data.is_locked == true or group_data.is_locked == "true" then return true end
  if tostring(group_data.send_permission or "everyone") == "admins" then return true end
  return false
end

local function extractGroupMemberNames(group_data)
  local list = {}
  if type(group_data.members) == "table" then
    for mk, mv in pairs(group_data.members) do
      local mname = type(mv) == "string" and mv or Uri.decode(tostring(mk))
      if mname and mname ~= "" then
        table.insert(list, mname)
      end
    end
  end
  return list
end

local function showBannedGroupDialog(gid, group_data, onExitDone)
  local gname = tostring(group_data.name or "Group")
  local layout = makeLayout(true, 18)
  layout.addView(makeText("Group: " .. gname, 16))
  layout.addView(makeText("This group is no longer available. This group has been banned.", 14))

  local exit_btn = makeButton("Exit Group")
  exit_btn.setBackgroundColor(0xFFD32F2F)
  exit_btn.setTextColor(0xFFFFFFFF)
  layout.addView(exit_btn, LinearLayout.LayoutParams(-1, -2))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Group Banned")
    .setView(layout)
    .setCancelable(false)
    .create()
  dialog.show()

  exit_btn.setOnClickListener(function()
    local hidden = getLocalHiddenMap("hidden_groups_json")
    hidden[gid] = true
    saveLocalHiddenMap("hidden_groups_json", hidden)
    http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. "/members/" .. encodeKey(current_username) .. ".json", function() end)
    showToast("Exited group.")
    dialog.dismiss()
    if onExitDone then onExitDone() end
  end)
end

local function showGroupInfoDialog(gid, group_data, onGroupUpdatedOrDeleted)
  local layout = makeLayout(true, 14)
  local scroll = ScrollView(activity)
  local inner = makeLayout(true, 8)
  scroll.addView(inner)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 520))

  local is_creator = isGroupCreator(group_data, current_username)
  local is_admin = isUserGroupAdmin(group_data, current_username)

  inner.addView(makeText("Group Name: " .. tostring(group_data.name or ""), 16))
  inner.addView(makeText("Creator: " .. getVerifiedName(group_data.creator or ""), 13))
  inner.addView(makeText("Description: " .. (tostring(group_data.description or "") ~= "" and tostring(group_data.description) or "None"), 13))
  inner.addView(makeText("Members Count: " .. tostring(group_data.members and table_size(group_data.members) or 1), 13))
  if type(group_data.pinned_message) == "table" and trim(tostring(group_data.pinned_message.text or "")) ~= "" then
    inner.addView(makeText("Pinned Message: " .. tostring(group_data.pinned_message.text or ""), 13))
  end

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Group Info & Settings")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()
  dialog.show()

  if is_admin then
    inner.addView(makeText("── Group Settings ──", 14))

    local desc_edit = EditText(activity)
    desc_edit.setHint("Edit Description (Max 200 chars)")
    desc_edit.setText(tostring(group_data.description or ""))
    inner.addView(desc_edit)

    local save_desc_btn = makeButton("Save Description")
    inner.addView(save_desc_btn)

    save_desc_btn.setOnClickListener(function()
      local new_d = trim(desc_edit.getText())
      if #new_d > 200 then new_d = new_d:sub(1, 200) end
      http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/description.json", "PUT", new_d, function(ok)
        if ok then
          group_data.description = new_d
          showToast("Description updated.")
        end
      end)
    end)

    local locked_now = isGroupLockedFlag(group_data)
    local lock_grp_btn = makeButton(locked_now and "Unlock Group (Currently Locked)" or "Lock Group (Only Admins Can Send)")
    inner.addView(lock_grp_btn)

    lock_grp_btn.setOnClickListener(function()
      local next_lock = not locked_now
      local next_perm = next_lock and "admins" or "everyone"
      http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/is_locked.json", "PUT", next_lock, function()
        http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/send_permission.json", "PUT", next_perm, function(ok)
          if ok then
            locked_now = next_lock
            group_data.is_locked = next_lock
            group_data.send_permission = next_perm
            lock_grp_btn.setText(locked_now and "Unlock Group (Currently Locked)" or "Lock Group (Only Admins Can Send)")
            showToast(locked_now and "Group locked. Only admins can send messages." or "Group unlocked.")
          end
        end)
      end)
    end)

    local cur_app = (group_data.approval_required == true or group_data.approval_required == "true")
    local app_btn = makeButton("Join Mode: " .. (cur_app and "Approval Required" or "Direct Join"))
    inner.addView(app_btn)

    app_btn.setOnClickListener(function()
      local next_app = not cur_app
      http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/approval_required.json", "PUT", next_app, function(ok)
        if ok then
          cur_app = next_app
          group_data.approval_required = next_app
          app_btn.setText("Join Mode: " .. (cur_app and "Approval Required" or "Direct Join"))
          showToast("Join mode updated.")
        end
      end)
    end)

    if isVerifiedUser(current_username) then
      local ban_grp_btn = makeButton("Ban This Group")
      ban_grp_btn.setBackgroundColor(0xFFD32F2F)
      ban_grp_btn.setTextColor(0xFFFFFFFF)
      inner.addView(ban_grp_btn, LinearLayout.LayoutParams(-1, -2))

      ban_grp_btn.setOnClickListener(function()
        http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/is_banned.json", "PUT", true, function(ok)
          if ok then
            group_data.is_banned = true
            showToast("Group has been banned.")
            dialog.dismiss()
            if onGroupUpdatedOrDeleted then onGroupUpdatedOrDeleted("banned") end
          end
        end)
      end)
    end

    if type(group_data.join_requests) == "table" and table_size(group_data.join_requests) > 0 then
      inner.addView(makeText("── Pending Join Requests ──", 14))
      for req_key, req_name in pairs(group_data.join_requests) do
        local actual_req_user = type(req_name) == "string" and req_name or Uri.decode(tostring(req_key))
        local req_row = makeLayout(false, 4)
        req_row.addView(makeText(actual_req_user, 14), LinearLayout.LayoutParams(0, -2, 1))
        local approve_btn = makeButton("Approve")
        local reject_btn = makeButton("Reject")
        req_row.addView(approve_btn)
        req_row.addView(reject_btn)
        inner.addView(req_row)

        approve_btn.setOnClickListener(function()
          http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/members/" .. encodeKey(actual_req_user) .. ".json", "PUT", actual_req_user, function()
            http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. "/join_requests/" .. encodeKey(actual_req_user) .. ".json", function()
              showToast(actual_req_user .. " approved!")
              dialog.dismiss()
            end)
          end)
        end)

        reject_btn.setOnClickListener(function()
          http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. "/join_requests/" .. encodeKey(actual_req_user) .. ".json", function()
            showToast("Request rejected.")
            dialog.dismiss()
          end)
        end)
      end
    end
  end

  inner.addView(makeText("── Group Members (" .. tostring(group_data.members and table_size(group_data.members) or 1) .. ") ──", 14))
  if type(group_data.members) == "table" then
    for m_key, m_val in pairs(group_data.members) do
      local m_name = type(m_val) == "string" and m_val or Uri.decode(tostring(m_key))
      local m_is_admin = isUserGroupAdmin(group_data, m_name)
      local m_row = makeLayout(false, 4)
      m_row.addView(makeText(getVerifiedName(m_name) .. (m_is_admin and " (Admin)" or ""), 13), LinearLayout.LayoutParams(0, -2, 1))

      if is_creator and trim(m_name):lower() ~= trim(current_username):lower() then
        local toggle_adm_btn = makeButton(m_is_admin and "Remove Admin" or "Make Admin")
        m_row.addView(toggle_adm_btn)
        toggle_adm_btn.setOnClickListener(function()
          if m_is_admin then
            http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. "/admins/" .. encodeKey(m_name) .. ".json", function()
              showToast(m_name .. " removed from admin.")
              dialog.dismiss()
            end)
          else
            http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/admins/" .. encodeKey(m_name) .. ".json", "PUT", true, function()
              showToast(m_name .. " is now Group Admin!")
              dialog.dismiss()
            end)
          end
        end)
      end
      inner.addView(m_row)
    end
  end

  if is_creator then
    local del_grp_btn = makeButton("Delete Group Permanently")
    del_grp_btn.setBackgroundColor(0xFFD32F2F)
    del_grp_btn.setTextColor(0xFFFFFFFF)
    inner.addView(del_grp_btn, LinearLayout.LayoutParams(-1, -2))

    del_grp_btn.setOnClickListener(function()
      http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. ".json", function(ok)
        http_delete(FIREBASE_URL .. "btp_group_messages/" .. gid .. ".json", function() end)
        showToast("Group deleted permanently for everyone.")
        dialog.dismiss()
        if onGroupUpdatedOrDeleted then onGroupUpdatedOrDeleted("deleted") end
      end)
    end)
  end
end

function openGroupChatDialog(gid, group_data)
  if (group_data.is_banned == true or group_data.is_banned == "true") and not isVerifiedUser(current_username) then
    showBannedGroupDialog(gid, group_data, nil)
    return
  end

  local layout = makeLayout(true, 10)

  local g_header = makeLayout(false, 5)
  local initial_gname = tostring(group_data.name or "Group")
  local initial_mem_cnt = group_data.members and table_size(group_data.members) or 1
  local title_tv = makeText(initial_gname .. " (" .. tostring(initial_mem_cnt) .. " members)", 15)
  title_tv.setTextColor(0xFF1E88E5)
  g_header.addView(title_tv, LinearLayout.LayoutParams(0, -2, 1))

  local more_btn = makeButton("More Options")
  g_header.addView(more_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(g_header)

  local pinned_banner = makeText("", 12)
  pinned_banner.setBackgroundColor(0xFFFFF8E1)
  pinned_banner.setTextColor(0xFF5D4037)
  pinned_banner.setPadding(8, 6, 8, 6)
  pinned_banner.setFocusable(true)
  pinned_banner.setVisibility(View.GONE)
  layout.addView(pinned_banner)

  local perm_banner = makeText("Only admin can send messages", 13)
  perm_banner.setTextColor(0xFFD32F2F)
  perm_banner.setPadding(6, 4, 6, 4)
  perm_banner.setVisibility(View.GONE)
  layout.addView(perm_banner)

  local scroll = ScrollView(activity)
  local chat_container = makeLayout(true, 8)
  scroll.addView(chat_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 310))

  local reply_banner = makeLayout(false, 8)
  reply_banner.setBackgroundColor(0xFFE0E0E0)
  reply_banner.setVisibility(View.GONE)

  local reply_text_preview = makeText("", 12)
  reply_banner.addView(reply_text_preview, LinearLayout.LayoutParams(0, -2, 1))
  local cancel_reply_btn = makeButton("Cancel Reply")
  reply_banner.addView(cancel_reply_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(reply_banner)

  local active_reply_target = nil
  cancel_reply_btn.setOnClickListener(function()
    active_reply_target = nil
    reply_banner.setVisibility(View.GONE)
  end)

  local input_layout = makeLayout(false, 4)
  local msg_input = EditText(activity)
  msg_input.setHint("Type a group message...")
  input_layout.addView(msg_input, LinearLayout.LayoutParams(0, -2, 1))

  local send_btn = makeButton("Send")
  input_layout.addView(send_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(input_layout)

  local voice_section = makeLayout(true, 6)
  voice_section.setBackgroundColor(0xFFECEFF1)

  local voice_status_tv = makeText("", 12)
  voice_status_tv.setVisibility(View.GONE)
  voice_section.addView(voice_status_tv)

  local voice_main_btn = makeButton("Record Voice Message")
  voice_section.addView(voice_main_btn, LinearLayout.LayoutParams(-1, -2))

  local group_voice_call_btn = makeButton("Live Group Voice Call")
  voice_section.addView(group_voice_call_btn, LinearLayout.LayoutParams(-1, -2))

  local voice_action_row = makeLayout(false, 2)
  voice_action_row.setVisibility(View.GONE)
  local voice_preview_btn = makeButton("Preview")
  local voice_send_preview_btn = makeButton("Send Voice")
  local voice_discard_btn = makeButton("Discard")

  voice_action_row.addView(voice_preview_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_action_row.addView(voice_send_preview_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_action_row.addView(voice_discard_btn, LinearLayout.LayoutParams(0, -2, 1))
  voice_section.addView(voice_action_row)
  layout.addView(voice_section)

  local go_back_btn = makeButton("Go Back")
  layout.addView(go_back_btn, LinearLayout.LayoutParams(-1, -2))

  local dialog = AlertDialog.Builder(activity)
    .setTitle(initial_gname .. " (" .. tostring(initial_mem_cnt) .. " members)")
    .setView(layout)
    .setCancelable(true)
    .create()
  dialog.show()

  local cache_key_grp = "grp_msg_cache_" .. tostring(gid)
  local is_grp_active = true
  local is_initial_load = true
  local grp_open_time = os.date("%Y%m%d%H%M%S")
  local seen_ids = {}
  local last_hash = ""
  local live_handler = Handler(Looper.getMainLooper())
  local live_runnable = nil
  local local_cleared_before = ""
  local ban_dialog_shown = false

  local voice_state = "idle"
  local media_recorder = nil
  local preview_player = nil
  local recorded_file_path = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_grp_rec.m4a"
  local record_seconds = 0
  local record_timer_handler = Handler(Looper.getMainLooper())
  local record_timer_runnable = nil

  local function stopPreviewPlayer()
    if preview_player ~= nil then
      pcall(function()
        if preview_player.isPlaying() then preview_player.stop() end
        preview_player.release()
      end)
      preview_player = nil
    end
    voice_preview_btn.setText("Preview")
  end

  local function resetVoiceUI()
    voice_state = "idle"
    record_seconds = 0
    if record_timer_runnable then
      pcall(function() record_timer_handler.removeCallbacks(record_timer_runnable) end)
      record_timer_runnable = nil
    end
    if media_recorder ~= nil then
      pcall(function()
        media_recorder.stop()
        media_recorder.release()
      end)
      media_recorder = nil
    end
    stopPreviewPlayer()
    voice_main_btn.setText("Record Voice Message")
    voice_main_btn.setVisibility(View.VISIBLE)
    voice_action_row.setVisibility(View.GONE)
    voice_status_tv.setVisibility(View.GONE)
  end

  local function closeGroupChat()
    is_grp_active = false
    resetVoiceUI()
    stopActiveVoicePlayer(false)
    current_voice_playlist = {}
    if live_handler and live_runnable then
      pcall(function() live_handler.removeCallbacks(live_runnable) end)
      live_runnable = nil
    end
  end

  go_back_btn.setOnClickListener(function()
    closeGroupChat()
    dialog.dismiss()
  end)

  dialog.setOnDismissListener(DialogInterface.OnDismissListener{ onDismiss = closeGroupChat })
  dialog.setOnCancelListener(DialogInterface.OnCancelListener{ onCancel = closeGroupChat })

  group_voice_call_btn.setOnClickListener(function()
    local gname_now = tostring(group_data.name or "Group")
    local members_arr = extractGroupMemberNames(group_data)
    initiateVoiceCall("group", gid, gname_now, members_arr)
  end)

  local function applyPinnedBanner()
    if type(group_data.pinned_message) == "table" and trim(tostring(group_data.pinned_message.text or "")) ~= "" then
      local ptxt = "Pinned: " .. tostring(group_data.pinned_message.text or "")
      pinned_banner.setText(ptxt)
      pinned_banner.setContentDescription(ptxt)
      pinned_banner.setVisibility(View.VISIBLE)
    else
      pinned_banner.setText("")
      pinned_banner.setVisibility(View.GONE)
    end
  end

  local function refreshGroupMetaAndOnline()
    if not is_grp_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "btp_groups/" .. gid .. ".json", function(s_g, r_g)
      if not is_grp_active then return end
      if not s_g or not r_g or r_g == "null" then
        showToast("This group was deleted by the creator.")
        closeGroupChat()
        dialog.dismiss()
        return
      end
      local ok_g, latest_g = pcall(cjson.decode, r_g)
      if ok_g and type(latest_g) == "table" then
        group_data = latest_g
        if (group_data.is_banned == true or group_data.is_banned == "true") and not isVerifiedUser(current_username) then
          if not ban_dialog_shown then
            ban_dialog_shown = true
            closeGroupChat()
            dialog.dismiss()
            showBannedGroupDialog(gid, group_data, nil)
          end
          return
        end

        applyPinnedBanner()

        local gname_str = tostring(group_data.name or "Group")
        local is_locked_grp = isGroupLockedFlag(group_data)
        local is_grp_adm = isUserGroupAdmin(group_data, current_username)
        local can_send = (not is_locked_grp) or is_grp_adm

        if not can_send then
          perm_banner.setText("Only admin can send messages")
          perm_banner.setVisibility(View.VISIBLE)
          input_layout.setVisibility(View.GONE)
          voice_section.setVisibility(View.GONE)
          reply_banner.setVisibility(View.GONE)
        else
          input_layout.setVisibility(View.VISIBLE)
          voice_section.setVisibility(View.VISIBLE)
          if is_locked_grp then
            perm_banner.setText("Group Locked for Members (Only admin can send messages)")
            perm_banner.setVisibility(View.VISIBLE)
          else
            perm_banner.setVisibility(View.GONE)
          end
        end

        local mem_cnt = group_data.members and table_size(group_data.members) or 1
        local combined_g_title = gname_str .. " (" .. tostring(mem_cnt) .. " members)"
        title_tv.setText(combined_g_title)
        dialog.setTitle(combined_g_title)
      end
    end)
  end

  local function touchGroupActivity()
    http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/last_activity_epoch.json", "PUT", os.time(), function() end)
  end

  local function renderGroupMessagesFromRaw(raw_json_str, force_refresh, from_network)
    local msg_list = {}
    local hash_builder = {}

    if raw_json_str and raw_json_str ~= "null" then
      local ok, data = pcall(cjson.decode, raw_json_str)
      if ok and type(data) == "table" then
        for k, v in pairs(data) do
          if type(v) == "table" then
            local traw = tostring(v.timestamp_raw or "")
            if local_cleared_before == "" or traw > local_cleared_before then
              v.id = k
              table.insert(msg_list, v)
              if from_network then
                markMessageSeenInFirebase(FIREBASE_URL .. "btp_group_messages/" .. gid .. "/" .. tostring(k))
              end
            end
          end
        end
      end
    end

    table.sort(msg_list, function(a, b)
      return tostring(a.timestamp_raw or a.timestamp or "") < tostring(b.timestamp_raw or b.timestamp or "")
    end)

    local new_rx_on_mine = false
    for _, m in ipairs(msg_list) do
      local r_pairs = {}
      if type(m.reactions) == "table" then
        for rk, rv in pairs(m.reactions) do
          table.insert(r_pairs, tostring(rk) .. "=" .. tostring(rv))
          local rx_unique = "gr_" .. tostring(m.id) .. "_" .. tostring(rk) .. "_" .. tostring(rv)
          if trim(tostring(m.sender or "")):lower() == trim(current_username):lower() and trim(Uri.decode(tostring(rk))):lower() ~= trim(current_username):lower() then
            if not is_initial_load and not known_reaction_keys[rx_unique] then
              new_rx_on_mine = true
            end
          end
          known_reaction_keys[rx_unique] = true
        end
      end
      table.sort(r_pairs)
      local seen_cnt = (type(m.seen_by) == "table") and table_size(m.seen_by) or 0
      local played_cnt = (type(m.played_by) == "table") and table_size(m.played_by) or 0
      local del_flag = (m.deleted_for_everyone == true or m.deleted_for_everyone == "true") and "1" or "0"
      table.insert(hash_builder, tostring(m.id) .. ":" .. del_flag .. ":" .. tostring(seen_cnt) .. ":" .. tostring(played_cnt) .. ":" .. table.concat(r_pairs, ","))
    end
    local pin_id = (type(group_data.pinned_message) == "table" and tostring(group_data.pinned_message.id or "")) or ""
    local cur_hash = table.concat(hash_builder, "|") .. ":" .. local_cleared_before .. ":pin" .. pin_id

    if new_rx_on_mine and is_grp_active and from_network then
      playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
    end

    if cur_hash == last_hash and not is_initial_load and not force_refresh then return end
    if active_voice_player ~= nil and not force_refresh then return end

    local new_incoming = false
    for _, m in ipairs(msg_list) do
      if not seen_ids[m.id] then
        seen_ids[m.id] = true
        if from_network and not is_initial_load and trim(tostring(m.sender or "")):lower() ~= trim(current_username):lower() and tostring(m.timestamp_raw or "") > grp_open_time then
          new_incoming = true
        end
      end
    end

    last_hash = cur_hash
    chat_container.removeAllViews()
    local grp_playlist = {}

    if #msg_list == 0 then
      chat_container.addView(makeText("No messages in this group yet.", 14))
    else
      local last_day = ""
      for _, msg in ipairs(msg_list) do
        local dl = getDayLabelFromRaw(msg.timestamp_raw)
        if dl ~= "" and dl ~= last_day then
          last_day = dl
          chat_container.addView(createAccessibleDayHeader(dl), LinearLayout.LayoutParams(-1, -2))
        end

        local is_me = (trim(tostring(msg.sender or "")):lower() == trim(current_username):lower())
        local is_deleted_all = (msg.deleted_for_everyone == true or msg.deleted_for_everyone == "true")
        local bubble = makeLayout(true, 8)
        bubble.setBackgroundColor(is_me and 0xFFDCF8C6 or 0xFFFFFFFF)
        bubble.setPadding(12, 10, 12, 10)

        if is_deleted_all then
          bubble.setClickable(false)
          bubble.setFocusable(true)
          local del_tv = makeText("This message was deleted", 13)
          del_tv.setTextColor(0xFF757575)
          bubble.addView(del_tv)
          chat_container.addView(bubble, LinearLayout.LayoutParams(-1, -2))
        else
          bubble.setClickable(true)
          bubble.setFocusable(true)

          if msg.reply_to and type(msg.reply_to) == "table" then
            local qbox = makeLayout(true, 6)
            qbox.setBackgroundColor(0xFFE8E8E8)
            qbox.addView(makeText("Replying to " .. getVerifiedName(msg.reply_to.sender) .. ":", 11))
            qbox.addView(makeText(tostring(msg.reply_to.text or ""), 12))
            bubble.addView(qbox, LinearLayout.LayoutParams(-1, -2))
          end

          local sender_lbl = is_me and "You" or getVerifiedName(msg.sender)
          if msg.msg_type == "voice" and msg.audio_base64 then
            local dstr = tostring(msg.audio_duration or "0") .. "s"
            bubble.addView(makeText(sender_lbl .. ": Voice message (" .. dstr .. ")", 14))
            local fb_msg_url = FIREBASE_URL .. "btp_group_messages/" .. gid .. "/" .. tostring(msg.id)
            buildVoiceBubblePlayer(bubble, msg, dstr, grp_playlist, fb_msg_url)
          else
            bubble.addView(makeText(sender_lbl .. ": " .. (msg.text or ""), 14))
          end

          renderClickableReactions(bubble, msg.reactions)

          local seen_txt = formatSeenByText(msg.seen_by)
          local meta_line = tostring(msg.timestamp or "")
          if seen_txt ~= "" then
            meta_line = meta_line .. " • " .. seen_txt
          end

          local mtv = makeText(meta_line, 11)
          mtv.setTextColor(0xFF777777)
          bubble.addView(mtv)
          chat_container.addView(bubble, LinearLayout.LayoutParams(-1, -2))

          bubble.setOnClickListener(View.OnClickListener{
            onClick = function()
              local can_reply_now = (not isGroupLockedFlag(group_data)) or isUserGroupAdmin(group_data, current_username)
              local opts = {"Add Reaction", "Delete for Me"}
              if can_reply_now then
                table.insert(opts, 1, "Reply")
              end
              if isGroupCreator(group_data, current_username) or isDeveloper(current_username) then
                local already_pinned = (type(group_data.pinned_message) == "table" and tostring(group_data.pinned_message.id or "") == tostring(msg.id))
                table.insert(opts, already_pinned and "Unpin Message" or "Pin Message")
              end
              if not is_me and trim(tostring(msg.sender or "")) ~= "" then
                table.insert(opts, "Private Chat with " .. tostring(msg.sender))
              end
              if is_me or isUserGroupAdmin(group_data, current_username) then
                table.insert(opts, "Delete for Everyone")
              end

              AlertDialog.Builder(activity)
                .setTitle("Message Options")
                .setItems(opts, DialogInterface.OnClickListener{
                  onClick = function(d_sub, which)
                    local choice = opts[which + 1]
                    if choice == "Reply" then
                      active_reply_target = { sender = msg.sender, text = msg.text }
                      reply_text_preview.setText("Replying to " .. tostring(msg.sender or "") .. ":\n" .. tostring(msg.text or ""))
                      reply_banner.setVisibility(View.VISIBLE)
                      msg_input.requestFocus()
                    elseif choice == "Pin Message" then
                      local pin_payload = {
                        id = msg.id,
                        sender = msg.sender,
                        text = tostring(msg.text or ("Voice message (" .. tostring(msg.audio_duration or "0") .. "s)"))
                      }
                      http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/pinned_message.json", "PUT", pin_payload, function(ok)
                        if ok then
                          group_data.pinned_message = pin_payload
                          applyPinnedBanner()
                          showToast("Message pinned.")
                          loadGroupMessages(true)
                        end
                      end)
                    elseif choice == "Unpin Message" then
                      http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. "/pinned_message.json", function(ok)
                        if ok then
                          group_data.pinned_message = nil
                          applyPinnedBanner()
                          showToast("Message unpinned.")
                          loadGroupMessages(true)
                        end
                      end)
                    elseif choice == "Add Reaction" then
                      local rlist = {"Love", "Like", "Haha", "Fire", "Clap", "Wow"}
                      AlertDialog.Builder(activity)
                        .setTitle("Select Reaction")
                        .setItems(rlist, DialogInterface.OnClickListener{
                          onClick = function(de, ew)
                            http_post_or_put(FIREBASE_URL .. "btp_group_messages/" .. gid .. "/" .. msg.id .. "/reactions/" .. encodeKey(current_username) .. ".json", "PUT", rlist[ew + 1], function(ok)
                              if ok then
                                playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
                                loadGroupMessages(true)
                              end
                            end)
                          end
                        }).show()
                    elseif choice == "Delete for Me" then
                      bubble.setVisibility(View.GONE)
                      showToast("Deleted for you.")
                    elseif choice == "Delete for Everyone" then
                      local del_url = FIREBASE_URL .. "btp_group_messages/" .. gid .. "/" .. msg.id
                      http_post_or_put(del_url .. "/deleted_for_everyone.json", "PUT", true, function(ok)
                        if ok then
                          http_post_or_put(del_url .. "/text.json", "PUT", "This message was deleted", function() end)
                          http_delete(del_url .. "/audio_base64.json", function() end)
                          showToast("Deleted for everyone.")
                          loadGroupMessages(true)
                        end
                      end)
                    elseif choice:find("Private Chat with ", 1, true) then
                      closeGroupChat()
                      dialog.dismiss()
                      openPersonalChat(msg.sender)
                    end
                  end
                }).show()
            end
          })
        end
      end
    end

    current_voice_playlist = grp_playlist

    if is_initial_load or new_incoming or force_refresh then
      scroll.post(Runnable({ run = function() scroll.fullScroll(ScrollView.FOCUS_DOWN) end }))
    end
    if new_incoming and is_grp_active and from_network then
      playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)
    end
    if from_network then
      is_initial_load = false
    end
  end

  local function loadGroupMessages(force_refresh)
    if not is_grp_active then return end
    if is_initial_load then
      local cached_g = loadOfflineCache(cache_key_grp)
      if cached_g then
        renderGroupMessagesFromRaw(cached_g, true, false)
      end
    end
    if not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "btp_group_messages/" .. gid .. '.json?orderBy="$key"&limitToLast=80', function(success, response)
      if not is_grp_active then return end
      if success and response and response ~= "null" then
        saveOfflineCache(cache_key_grp, response)
      end
      renderGroupMessagesFromRaw(success and response or nil, force_refresh, true)
    end)
  end

  local function executeGroupVoiceSendAfterPreSound(duration_sec)
    voice_status_tv.setText("Sending voice message...")
    voice_status_tv.setVisibility(View.VISIBLE)
    voice_main_btn.setEnabled(false)
    voice_send_preview_btn.setEnabled(false)

    local b64_audio = encodeFileToBase64(recorded_file_path)
    if not b64_audio or b64_audio == "" then
      showToast("Recording failed or empty audio.")
      voice_main_btn.setEnabled(true)
      voice_send_preview_btn.setEnabled(true)
      resetVoiceUI()
      return
    end

    local payload = {
      sender = current_username,
      msg_type = "voice",
      text = "Voice message (" .. tostring(duration_sec) .. "s)",
      audio_base64 = b64_audio,
      audio_duration = duration_sec,
      timestamp = os.date("%I:%M %p"),
      timestamp_raw = os.date("%Y%m%d%H%M%S")
    }
    if active_reply_target ~= nil then
      payload.reply_to = active_reply_target
      active_reply_target = nil
      reply_banner.setVisibility(View.GONE)
    end

    http_post_or_put(FIREBASE_URL .. "btp_group_messages/" .. gid .. ".json", "POST", payload, function(success)
      voice_main_btn.setEnabled(true)
      voice_send_preview_btn.setEnabled(true)
      resetVoiceUI()
      if success then
        touchGroupActivity()
        playSound(SOUND_SEND, nil, ToneGenerator.TONE_PROP_BEEP, false)
        loadGroupMessages(true)
      else
        showToast("Failed to send voice message.")
      end
    end)
  end

  local function sendVoicePayload(duration_sec)
    if notifyServerDownIfNeeded() then
      resetVoiceUI()
      return
    end
    if isGroupLockedFlag(group_data) and not isUserGroupAdmin(group_data, current_username) then
      showToast("Only admin can send messages")
      resetVoiceUI()
      return
    end
    playSound(SOUND_VOICE_PRE_SEND, function()
      executeGroupVoiceSendAfterPreSound(duration_sec)
    end, ToneGenerator.TONE_PROP_PROMPT, false)
  end

  local function finishRecordingToState(target_mode)
    local final_sec = record_seconds
    if final_sec < 1 then final_sec = 1 end
    if record_timer_runnable then
      pcall(function() record_timer_handler.removeCallbacks(record_timer_runnable) end)
      record_timer_runnable = nil
    end
    if media_recorder ~= nil then
      pcall(function()
        media_recorder.stop()
        media_recorder.release()
      end)
      media_recorder = nil
    end
    if target_mode == "send" then
      sendVoicePayload(final_sec)
    else
      voice_state = "preview"
      voice_main_btn.setVisibility(View.GONE)
      voice_action_row.setVisibility(View.VISIBLE)
      voice_preview_btn.setText("Preview (" .. tostring(final_sec) .. "s)")
      voice_status_tv.setText("Recorded " .. tostring(final_sec) .. "s")
      voice_status_tv.setVisibility(View.VISIBLE)
    end
  end

  voice_main_btn.setOnClickListener(function()
    if notifyServerDownIfNeeded() then return end
    if isGroupLockedFlag(group_data) and not isUserGroupAdmin(group_data, current_username) then
      showToast("Only admin can send messages")
      return
    end

    if voice_state == "idle" then
      stopActiveVoicePlayer(false)
      local old_f = File(recorded_file_path)
      if old_f.exists() then old_f.delete() end

      media_recorder = startHighClarityRecording(recorded_file_path)
      if media_recorder == nil then
        showToast("Microphone permission required.")
        return
      end

      voice_state = "recording"
      record_seconds = 0
      voice_main_btn.setText("Stop and Send Voice")
      voice_action_row.setVisibility(View.VISIBLE)
      voice_preview_btn.setText("Stop and Preview")
      voice_send_preview_btn.setText("Send Now")
      voice_discard_btn.setText("Discard")
      voice_status_tv.setText("Recording: 0s")
      voice_status_tv.setVisibility(View.VISIBLE)

      record_timer_runnable = Runnable({
        run = function()
          if voice_state == "recording" and is_grp_active then
            record_seconds = record_seconds + 1
            voice_status_tv.setText("Recording: " .. tostring(record_seconds) .. "s")
            if record_seconds >= MAX_VOICE_SECONDS then
              finishRecordingToState("send")
            else
              record_timer_handler.postDelayed(record_timer_runnable, 1000)
            end
          end
        end
      })
      record_timer_handler.postDelayed(record_timer_runnable, 1000)
    elseif voice_state == "recording" then
      finishRecordingToState("send")
    end
  end)

  voice_preview_btn.setOnClickListener(function()
    if voice_state == "recording" then
      finishRecordingToState("preview")
      voice_send_preview_btn.setText("Send Voice")
    elseif voice_state == "preview" then
      if preview_player ~= nil then
        stopPreviewPlayer()
        return
      end
      pcall(function()
        local f = File(recorded_file_path)
        if f.exists() then
          preview_player = MediaPlayer()
          preview_player.setDataSource(recorded_file_path)
          preview_player.prepare()
          preview_player.start()
          voice_preview_btn.setText("Stop Preview")
          preview_player.setOnCompletionListener(MediaPlayer.OnCompletionListener{ onCompletion = stopPreviewPlayer })
        end
      end)
    end
  end)

  voice_send_preview_btn.setOnClickListener(function()
    if voice_state == "recording" then
      finishRecordingToState("send")
    elseif voice_state == "preview" then
      stopPreviewPlayer()
      sendVoicePayload(record_seconds > 0 and record_seconds or 1)
    end
  end)

  voice_discard_btn.setOnClickListener(function()
    playSound(SOUND_DISCARD, nil, ToneGenerator.TONE_PROP_NACK, false)
    resetVoiceUI()
    showToast("Voice recording discarded.")
  end)

  more_btn.setOnClickListener(function()
    local is_creator = isGroupCreator(group_data, current_username)
    local choices = {"Group Info & Settings", "Clear Chat (For Me)", "Delete / Hide Group (For Me)"}
    if type(group_data.pinned_message) == "table" and (is_creator or isDeveloper(current_username)) then
      table.insert(choices, "Unpin Current Message")
    end
    if is_creator or isDeveloper(current_username) then
      table.insert(choices, "Delete Group Permanently (For Everyone)")
    end

    AlertDialog.Builder(activity)
      .setTitle("More Options")
      .setItems(choices, DialogInterface.OnClickListener{
        onClick = function(dc, w)
          local sel = choices[w + 1]
          if sel == "Group Info & Settings" then
            showGroupInfoDialog(gid, group_data, function(action_res)
              if action_res == "deleted" or action_res == "banned" then
                closeGroupChat()
                dialog.dismiss()
              else
                refreshGroupMetaAndOnline()
              end
            end)
          elseif sel == "Unpin Current Message" then
            http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. "/pinned_message.json", function(ok)
              if ok then
                group_data.pinned_message = nil
                applyPinnedBanner()
                showToast("Message unpinned.")
              end
            end)
          elseif sel == "Clear Chat (For Me)" then
            local_cleared_before = os.date("%Y%m%d%H%M%S")
            last_hash = ""
            loadGroupMessages(true)
            showToast("Group chat cleared for you.")
          elseif sel == "Delete / Hide Group (For Me)" then
            local hidden = getLocalHiddenMap("hidden_groups_json")
            hidden[gid] = true
            saveLocalHiddenMap("hidden_groups_json", hidden)
            http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. "/members/" .. encodeKey(current_username) .. ".json", function() end)
            showToast("Group removed from your list.")
            closeGroupChat()
            dialog.dismiss()
          elseif sel == "Delete Group Permanently (For Everyone)" then
            http_delete(FIREBASE_URL .. "btp_groups/" .. gid .. ".json", function()
              http_delete(FIREBASE_URL .. "btp_group_messages/" .. gid .. ".json", function() end)
              showToast("Group deleted permanently for all members.")
              closeGroupChat()
              dialog.dismiss()
            end)
          end
        end
      }).show()
  end)

  refreshGroupMetaAndOnline()
  loadGroupMessages(true)

  live_runnable = Runnable({
    run = function()
      if is_grp_active and isAppForeground then
        refreshGroupMetaAndOnline()
        loadGroupMessages(false)
        live_handler.postDelayed(live_runnable, ROOM_POLL_INTERVAL_MS)
      end
    end
  })
  live_handler.postDelayed(live_runnable, ROOM_POLL_INTERVAL_MS)

  send_btn.setOnClickListener(function()
    if notifyServerDownIfNeeded() then return end
    if isGroupLockedFlag(group_data) and not isUserGroupAdmin(group_data, current_username) then
      showToast("Only admin can send messages")
      return
    end

    local text = trim(msg_input.getText())
    if text == "" then return end

    send_btn.setEnabled(false)
    local payload = {
      sender = current_username,
      msg_type = "text",
      text = text,
      timestamp = os.date("%I:%M %p"),
      timestamp_raw = os.date("%Y%m%d%H%M%S")
    }
    if active_reply_target ~= nil then
      payload.reply_to = active_reply_target
      active_reply_target = nil
      reply_banner.setVisibility(View.GONE)
    end

    http_post_or_put(FIREBASE_URL .. "btp_group_messages/" .. gid .. ".json", "POST", payload, function(success)
      send_btn.setEnabled(true)
      if success then
        touchGroupActivity()
        playSound(SOUND_SEND, nil, ToneGenerator.TONE_PROP_BEEP, false)
        msg_input.setText("")
        loadGroupMessages(true)
      else
        showToast("Failed to send message.")
      end
    end)
  end)
end

function showGroupsListDialog()
  local layout = makeLayout(true, 15)

  local top_bar = makeLayout(false, 4)
  local info_lbl = makeText("Community Groups", 15)
  top_bar.addView(info_lbl, LinearLayout.LayoutParams(0, -2, 1))
  local create_grp_btn = makeButton("Create Group")
  top_bar.addView(create_grp_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(top_bar)

  local scroll = ScrollView(activity)
  local list_container = makeLayout(true, 8)
  scroll.addView(list_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 500))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Groups")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()
  dialog.show()

  local function renderGroupsFromRaw(r_g)
    list_container.removeAllViews()
    local hidden_map = getLocalHiddenMap("hidden_groups_json")

    local groups_arr = {}
    if r_g and r_g ~= "null" then
      local ok_g, gdata = pcall(cjson.decode, r_g)
      if ok_g and type(gdata) == "table" then
        for gid, g in pairs(gdata) do
          if type(g) == "table" then
            local is_h = hidden_map[gid]
            local is_b = (g.is_banned == true or g.is_banned == "true")
            if not is_h or (is_b and not isVerifiedUser(current_username)) then
              g.id = gid
              table.insert(groups_arr, g)
            end
          end
        end
      end
    end

    table.sort(groups_arr, function(a, b)
      return tonumber(a.last_activity_epoch or 0) > tonumber(b.last_activity_epoch or 0)
    end)

    if #groups_arr == 0 then
      list_container.addView(makeText("No groups created yet. Tap Create Group to start one!", 14))
      return
    end

    local my_norm = trim(current_username):lower()

    for _, g in ipairs(groups_arr) do
      local card = makeLayout(true, 10)
      card.setBackgroundColor(0xFFEEEEEE)
      card.setPadding(12, 10, 12, 10)
      card.setClickable(true)
      card.setFocusable(true)

      local is_banned_g = (g.is_banned == true or g.is_banned == "true")
      local is_member = false
      local is_pending = false
      local mem_cnt = g.members and table_size(g.members) or 1

      if type(g.members) == "table" then
        for mk, mv in pairs(g.members) do
          local mname = type(mv) == "string" and mv or Uri.decode(tostring(mk))
          if trim(mname):lower() == my_norm then
            is_member = true
          end
        end
      end

      if type(g.join_requests) == "table" then
        for rk, rv in pairs(g.join_requests) do
          local rname = type(rv) == "string" and rv or Uri.decode(tostring(rk))
          if trim(rname):lower() == my_norm then
            is_pending = true
          end
        end
      end

      local gtitle_txt = tostring(g.name or "Unnamed Group")
      local gtitle = makeText(gtitle_txt, 16)
      gtitle.setTextColor(is_banned_g and 0xFFD32F2F or 0xFF1E88E5)
      card.addView(gtitle)

      local creator_line = tostring(mem_cnt) .. " members • Creator: " .. getVerifiedName(g.creator or "")
      if not is_banned_g and tostring(g.description or "") ~= "" then
        creator_line = creator_line .. " • " .. tostring(g.description)
      end
      card.addView(makeText(creator_line, 12))

      local action_btn
      if is_banned_g and not isVerifiedUser(current_username) then
        action_btn = makeButton("Group Banned - Tap to View")
      elseif is_member or isVerifiedUser(current_username) then
        action_btn = makeButton("Open Group")
      elseif is_pending then
        action_btn = makeButton("Cancel Join Request")
      elseif g.approval_required == true or g.approval_required == "true" then
        action_btn = makeButton("Request to Join")
      else
        action_btn = makeButton("Join Group")
      end
      card.addView(action_btn, LinearLayout.LayoutParams(-1, -2))

      local function handleGroupSelect()
        if is_banned_g and not isVerifiedUser(current_username) then
          dialog.dismiss()
          showBannedGroupDialog(g.id, g, function()
            showGroupsListDialog()
          end)
        elseif is_member or isVerifiedUser(current_username) then
          dialog.dismiss()
          openGroupChatDialog(g.id, g)
        elseif is_pending then
          http_delete(FIREBASE_URL .. "btp_groups/" .. g.id .. "/join_requests/" .. encodeKey(current_username) .. ".json", function(ok)
            if ok then
              showToast("Join request cancelled.")
              loadAllGroups()
            end
          end)
        elseif g.approval_required == true or g.approval_required == "true" then
          http_post_or_put(FIREBASE_URL .. "btp_groups/" .. g.id .. "/join_requests/" .. encodeKey(current_username) .. ".json", "PUT", current_username, function(ok)
            if ok then
              showToast("Join request sent to group admin.")
              loadAllGroups()
            end
          end)
        else
          http_post_or_put(FIREBASE_URL .. "btp_groups/" .. g.id .. "/members/" .. encodeKey(current_username) .. ".json", "PUT", current_username, function(ok)
            if ok then
              showToast("Joined group!")
              dialog.dismiss()
              openGroupChatDialog(g.id, g)
            end
          end)
        end
      end

      action_btn.setOnClickListener(handleGroupSelect)
      card.setOnClickListener(function()
        if is_member or isVerifiedUser(current_username) then
          dialog.dismiss()
          openGroupChatDialog(g.id, g)
        else
          showMessage(
            gtitle_txt,
            "Members: " .. tostring(mem_cnt)
            .. "\nCreator: " .. getVerifiedName(g.creator or "")
            .. (tostring(g.description or "") ~= "" and ("\nDescription: " .. tostring(g.description)) or "")
            .. (is_pending and "\nStatus: Join request pending." or "")
          )
        end
      end)

      list_container.addView(card, LinearLayout.LayoutParams(-1, -2))
    end
  end

  function loadAllGroups()
    local cached_grps = loadOfflineCache("btp_groups_list_cache")
    if cached_grps then
      renderGroupsFromRaw(cached_grps)
    else
      list_container.addView(makeText("Loading groups...", 14))
    end
    if not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "btp_groups.json", function(s_g, r_g)
      if s_g and r_g and r_g ~= "null" then
        saveOfflineCache("btp_groups_list_cache", r_g)
        renderGroupsFromRaw(r_g)
      elseif not cached_grps then
        renderGroupsFromRaw(nil)
      end
    end)
  end

  create_grp_btn.setOnClickListener(function()
    showCreateGroupDialog(function()
      loadAllGroups()
    end)
  end)

  loadAllGroups()
endend
-- ========================================================
-- CHAT HUB (CLEAN BTP VOICE ROOM CARD + NEW MESSAGE COUNTER)
-- ========================================================

function showResourceChatDialog()
  local layout = makeLayout(true, 15)

  local top_actions = makeLayout(false, 4)
  local more_chat_btn = makeButton("More Options (Create Group & Personal Assistant)")
  top_actions.addView(more_chat_btn, LinearLayout.LayoutParams(-1, -2))
  layout.addView(top_actions)

  local assistant_card = makeLayout(true, 12)
  assistant_card.setBackgroundColor(0xFFEDE7F6)
  local ast_title = makeText("BTP Assistant", 16)
  ast_title.setTextColor(0xFF4A148C)
  assistant_card.addView(ast_title)
  assistant_card.addView(makeText("Smart help for app features, Lua code & Q&A", 12))
  layout.addView(assistant_card, LinearLayout.LayoutParams(-1, -2))

  local scroll = ScrollView(activity)
  local users_container = makeLayout(true, 10)
  scroll.addView(users_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 470))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Chat")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()

  assistant_card.setOnClickListener(function()
    pcall(function() dialog.dismiss() end)
    openBTPAssistantDialog()
  end)

  dialog.show()

  more_chat_btn.setOnClickListener(function()
    local opts = {"Create New Group", "View All Groups", "Personal Chat BTP Assistant (Auto-Reply & Train)"}
    AlertDialog.Builder(activity)
      .setTitle("More Options")
      .setItems(opts, DialogInterface.OnClickListener{
        onClick = function(d, w)
          if w == 0 then
            showCreateGroupDialog(function()
              dialog.dismiss()
              showGroupsListDialog()
            end)
          elseif w == 1 then
            dialog.dismiss()
            showGroupsListDialog()
          else
            showPersonalAssistantSetupDialog()
          end
        end
      }).show()
  end)

  local function countUnreadVoiceRoomMessages(vr_raw)
    if not vr_raw or vr_raw == "null" then return 0 end
    local ok, data = pcall(cjson.decode, vr_raw)
    if not ok or type(data) ~= "table" then return 0 end
    local list = {}
    for k, v in pairs(data) do
      if type(v) == "table" then
        v.id = k
        table.insert(list, v)
      end
    end
    table.sort(list, function(a, b)
      return tostring(a.timestamp_raw or a.timestamp or "") < tostring(b.timestamp_raw or b.timestamp or "")
    end)
    local last_seen_id = tostring(sp.getString("last_seen_vr_msg_id", ""))
    if last_seen_id == "" then return 0 end
    local found_last = false
    local unread = 0
    local my_low = trim(current_username):lower()
    for _, m in ipairs(list) do
      if found_last then
        if trim(tostring(m.sender or "")):lower() ~= my_low then
          unread = unread + 1
        end
      elseif tostring(m.id) == last_seen_id then
        found_last = true
      end
    end
    return unread
  end

  local function renderChatHubLists(r_reg, r_vr)
    users_container.removeAllViews()

    local unread_vr = countUnreadVoiceRoomMessages(r_vr)
    local voice_room_card = makeLayout(true, 12)
    voice_room_card.setBackgroundColor(0xFFE3F2FD)

    local vr_title_str = "BTP Voice Room"
    if unread_vr == 1 then
      vr_title_str = "BTP Voice Room (1 new message)"
    elseif unread_vr > 1 then
      vr_title_str = "BTP Voice Room (" .. tostring(unread_vr) .. " new messages)"
    end
    if public_room_locked and canBypassRoomLock(current_username) then
      vr_title_str = vr_title_str .. " • Locked"
    end

    local vr_title = makeText(vr_title_str, 16)
    vr_title.setTextColor(0xFF0D47A1)
    voice_room_card.addView(vr_title)
    users_container.addView(voice_room_card, LinearLayout.LayoutParams(-1, -2))

    voice_room_card.setOnClickListener(function()
      dialog.dismiss()
      openBtpVoiceRoomDialog()
    end)

    local groups_card = makeLayout(true, 12)
    groups_card.setBackgroundColor(0xFFE8F5E9)
    local grp_title = makeText("View Groups", 16)
    grp_title.setTextColor(0xFF1B5E20)
    groups_card.addView(grp_title)
    users_container.addView(groups_card, LinearLayout.LayoutParams(-1, -2))

    groups_card.setOnClickListener(function()
      dialog.dismiss()
      showGroupsListDialog()
    end)

    local user_map = {}

    if r_reg and r_reg ~= "null" then
      local ok, data = pcall(cjson.decode, r_reg)
      if ok and type(data) == "table" then
        for k, v in pairs(data) do
          local uname = (type(v) == "table" and v.username) or k
          local epoch = (type(v) == "table" and v.last_active_epoch) or 0
          if uname and uname ~= "" then
            user_map[uname] = epoch
          end
        end
      end
    end

    user_map["Ibrahim Ansari"] = user_map["Ibrahim Ansari"] or os.time()

    local user_list = {}
    for u, _ in pairs(user_map) do
      if trim(u):lower() ~= trim(current_username):lower() then
        table.insert(user_list, u)
      end
    end

    table.sort(user_list, function(a, b)
      local ep_a = tonumber(user_map[a] or 0)
      local ep_b = tonumber(user_map[b] or 0)
      if ep_a ~= ep_b then return ep_a > ep_b end
      return tostring(a):lower() < tostring(b):lower()
    end)

    for _, u in ipairs(user_list) do
      local card = makeLayout(true, 10)
      card.setBackgroundColor(0xFFEEEEEE)
      card.setPadding(14, 12, 14, 12)
      card.setFocusable(true)
      card.setClickable(true)

      local name_tv = makeText(getVerifiedName(u), 16)
      name_tv.setTextColor(0xFF1E88E5)
      card.addView(name_tv)

      local sub_tv = makeText("Tap to open personal chat & live voice call", 12)
      sub_tv.setTextColor(0xFF666666)
      card.addView(sub_tv)

      users_container.addView(card, LinearLayout.LayoutParams(-1, -2))

      card.setOnClickListener(function()
        dialog.dismiss()
        openPersonalChat(u)
      end)
    end
  end

  local cached_reg = loadOfflineCache("registered_users_cache")
  local cached_vr = loadOfflineCache("btp_voice_room_cache")
  if cached_reg or cached_vr then
    renderChatHubLists(cached_reg, cached_vr)
  else
    users_container.addView(makeText("Loading chats...", 14))
  end

  if isNetworkAvailable() then
    syncServerAndRoomSettings(function()
      http_get(FIREBASE_URL .. "registered_users.json", function(s_reg, r_reg)
        if s_reg and r_reg and r_reg ~= "null" then
          saveOfflineCache("registered_users_cache", r_reg)
        end
        http_get(FIREBASE_URL .. 'btp_voice_room.json?orderBy="$key"&limitToLast=30', function(s_vr, r_vr)
          if s_vr and r_vr and r_vr ~= "null" then
            saveOfflineCache("btp_voice_room_cache", r_vr)
          end
          renderChatHubLists(s_reg and r_reg or cached_reg, s_vr and r_vr or cached_vr)
        end)
      end)
    end)
  end
end

-- ========================================================
-- SAFE CODE TESTER HELPER (FOR ALL USERS & CREATORS)
-- ========================================================

local function runLuaCodeTestPreview(code_str, onResultCb)
  local clean_code = trim(tostring(code_str or ""))
  if clean_code == "" then
    if onResultCb then onResultCb(false, "Code is empty. Please paste Lua code first.") end
    return false, "Code is empty."
  end

  local loader = loadstring or load
  if not loader then
    if onResultCb then onResultCb(true, "Syntax check passed.") end
    return true, "Syntax check passed."
  end

  local fn, syntax_err = loader(clean_code, "BTP_Test_Code")
  if not fn then
    local err_msg = "Syntax Error:\n" .. tostring(syntax_err)
    if onResultCb then onResultCb(false, err_msg) end
    return false, err_msg
  end

  local run_ok, runtime_err = pcall(fn)
  if not run_ok then
    local err_msg = "Runtime Error:\n" .. tostring(runtime_err)
    if onResultCb then onResultCb(false, err_msg) end
    return false, err_msg
  end

  if onResultCb then onResultCb(true, "Code tested successfully! Zero errors found.") end
  return true, "Code tested successfully! Zero errors found."
end

-- ========================================================
-- ABOUT CODE DIALOG (LIKE THIS CODE + TEST CODE + COMMENTS)
-- ========================================================

local function formatCodeLikesSummary(likes_tbl)
  if type(likes_tbl) ~= "table" or table_size(likes_tbl) == 0 then
    return "Like this code"
  end
  local names = {}
  for lk, _ in pairs(likes_tbl) do
    table.insert(names, Uri.decode(tostring(lk)))
  end
  local total = #names
  if total == 1 then
    return "Like this code • Liked by " .. names[1]
  elseif total == 2 then
    return "Like this code • Liked by " .. names[1] .. " along with 1 other person"
  else
    return "Like this code • Liked by " .. names[1] .. " along with " .. tostring(total - 1) .. " other people"
  end
end

function showAboutCodeDialog(item)
  local layout = makeLayout(true, 15)
  local main_scroll = ScrollView(activity)
  local inner = makeLayout(true, 10)

  local likes_summary = formatCodeLikesSummary(item.likes)
  local seen_count = item.views and table_size(item.views) or 1

  inner.addView(makeText(
    "Title: " .. (item.title or "Untitled Code") .. "\n"
    .. "Description: " .. (item.desc or "No description") .. "\n"
    .. "Author: " .. getVerifiedName(item.author or "Anonymous") .. "\n"
    .. "Date: " .. (item.timestamp or "N/A") .. "\n"
    .. "Views: " .. tostring(seen_count) .. " • " .. likes_summary,
    14
  ))

  inner.addView(makeText("Complete Lua Source Code:", 16))

  local nav_scroll_row = makeLayout(false, 4)
  local scroll_to_top_btn = makeButton("Scroll to Top")
  local scroll_to_bottom_btn = makeButton("Scroll to Bottom")
  nav_scroll_row.addView(scroll_to_top_btn, LinearLayout.LayoutParams(0, -2, 1))
  nav_scroll_row.addView(scroll_to_bottom_btn, LinearLayout.LayoutParams(0, -2, 1))
  inner.addView(nav_scroll_row)

  local code_view = makeText(item.code or "", 13)
  code_view.setTextIsSelectable(true)
  code_view.setPadding(10, 10, 10, 10)
  code_view.setBackgroundColor(0xFFF9F9F9)
  inner.addView(code_view)

  scroll_to_top_btn.setOnClickListener(function()
    main_scroll.fullScroll(ScrollView.FOCUS_UP)
  end)

  scroll_to_bottom_btn.setOnClickListener(function()
    main_scroll.fullScroll(ScrollView.FOCUS_DOWN)
  end)

  local action_row_1 = makeLayout(false, 4)
  local copy_button = makeButton("Copy Code")
  local test_code_button = makeButton("Test Code")
  action_row_1.addView(copy_button, LinearLayout.LayoutParams(0, -2, 1))
  action_row_1.addView(test_code_button, LinearLayout.LayoutParams(0, -2, 1))
  inner.addView(action_row_1)

  local like_button = makeButton("Like this code (+1 Creator Point)")
  inner.addView(like_button)

  inner.addView(makeText("Comments & Discussion", 16))

  local comments_container = makeLayout(true, 8)
  local comment_input = EditText(activity)
  comment_input.setHint("Write a comment or reply...")

  local function renderComments()
    comments_container.removeAllViews()
    local has_comments = false
    if item.comments then
      for _, c in pairs(item.comments) do
        has_comments = true
        local c_box = makeLayout(true, 6)
        c_box.setBackgroundColor(0xFFF2F2F2)
        c_box.addView(makeText(getVerifiedName(c.user or "Anonymous") .. ": " .. (c.text or ""), 13))
        local reply_btn = makeButton("Reply")
        c_box.addView(reply_btn, LinearLayout.LayoutParams(-2, -2))
        comments_container.addView(c_box, LinearLayout.LayoutParams(-1, -2))

        reply_btn.setOnClickListener(function()
          comment_input.setText("@" .. (c.user or "Anonymous") .. " ")
          comment_input.setSelection(comment_input.getText().length())
        end)
      end
    end
    if not has_comments then
      comments_container.addView(makeText("No comments yet.", 13))
    end
  end

  renderComments()
  inner.addView(comments_container)
  inner.addView(comment_input)

  local submit_comment_btn = makeButton("Submit Comment")
  inner.addView(submit_comment_btn)

  main_scroll.addView(inner)
  layout.addView(main_scroll, LinearLayout.LayoutParams(-1, 550))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Code Details")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()

  dialog.show()

  copy_button.setOnClickListener(function() copyCode(item.code or "") end)

  test_code_button.setOnClickListener(function()
    runLuaCodeTestPreview(item.code or "", function(ok, msg)
      showMessage(ok and "Code Test Passed" or "Code Test Error", msg)
    end)
  end)

  like_button.setOnClickListener(function()
    if not item.id then return end
    local key = encodeKey(current_username)
    local url = FIREBASE_URL .. "codes/" .. item.id .. "/likes/" .. key .. ".json"
    http_post_or_put(url, "PUT", true, function(ok)
      if ok then
        playSound(SOUND_LIKE, nil, ToneGenerator.TONE_PROP_ACK, false)
        if trim(tostring(item.author or "")) ~= "" then
          local pt_url = FIREBASE_URL .. "creator_points/" .. encodeKey(item.author) .. "/" .. tostring(item.id) .. "_" .. key .. ".json"
          http_post_or_put(pt_url, "PUT", 1, function() end)
        end
        showToast("Liked! Creator received +1 point.")
        dialog.dismiss()
        loadCodesData()
      end
    end)
  end)

  submit_comment_btn.setOnClickListener(function()
    local text = trim(comment_input.getText())
    if text == "" then showToast("Please write something.") return end
    if not item.id then return end

    local payload = {
      user = current_username,
      text = text,
      timestamp = os.date("%Y-%m-%d %H:%M:%S")
    }

    http_post_or_put(FIREBASE_URL .. "codes/" .. item.id .. "/comments.json", "POST", payload, function(ok)
      if ok then
        playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP, false)
        showToast("Comment submitted.")
        dialog.dismiss()
        loadCodesData()
      end
    end)
  end)
end

-- ========================================================
-- CODES FEED VIEW (WITH OFFLINE CACHE FOR SLOW/NO INTERNET)
-- ========================================================

local feed_container

local function renderFeedList(list_data)
  if not feed_container then return end
  feed_container.removeAllViews()

  if #list_data == 0 then
    local empty = makeText("No Lua codes uploaded yet.", 16)
    empty.setPadding(20, 30, 20, 30)
    feed_container.addView(empty)
    return
  end

  for _, item in ipairs(list_data) do
    local card = makeLayout(true, 14)
    card.setBackgroundColor(0xFFFFFFFF)

    card.addView(makeText(item.title or "Untitled Code", 18))
    card.addView(makeText("Description: " .. (item.desc or "No description"), 13))
    card.addView(makeText("Uploaded by: " .. getVerifiedName(item.author or "Anonymous"), 13))
    card.addView(makeText("Date: " .. (item.timestamp or "N/A"), 12))

    local like_summary_tv = makeText(formatCodeLikesSummary(item.likes), 13)
    like_summary_tv.setTextColor(0xFF1565C0)
    like_summary_tv.setPadding(0, 4, 0, 4)
    card.addView(like_summary_tv)

    like_summary_tv.setOnClickListener(function()
      if not item.id then return end
      local key = encodeKey(current_username)
      local url = FIREBASE_URL .. "codes/" .. item.id .. "/likes/" .. key .. ".json"
      http_post_or_put(url, "PUT", true, function(ok)
        if ok then
          playSound(SOUND_LIKE, nil, ToneGenerator.TONE_PROP_ACK, false)
          if trim(tostring(item.author or "")) ~= "" then
            local pt_url = FIREBASE_URL .. "creator_points/" .. encodeKey(item.author) .. "/" .. tostring(item.id) .. "_" .. key .. ".json"
            http_post_or_put(pt_url, "PUT", 1, function() end)
          end
          showToast("Liked! +1 point to " .. tostring(item.author or "Creator"))
          loadCodesData()
        end
      end)
    end)

    local preview = item.code or ""
    if #preview > 250 then preview = preview:sub(1, 250) .. "\n\n...Preview shortened" end
    local preview_view = makeText("Code Preview:\n" .. preview, 12)
    preview_view.setTextIsSelectable(true)
    card.addView(preview_view)

    local btn_row = makeLayout(false, 4)
    local copy_btn = makeButton("Copy Code")
    local test_btn = makeButton("Test Code")
    local details_btn = makeButton("View / Comment")

    btn_row.addView(copy_btn, LinearLayout.LayoutParams(0, -2, 1))
    btn_row.addView(test_btn, LinearLayout.LayoutParams(0, -2, 1))
    btn_row.addView(details_btn, LinearLayout.LayoutParams(0, -2, 1))
    card.addView(btn_row)

    copy_btn.setOnClickListener(function()
      playSound(SOUND_CODE_HIT, nil, ToneGenerator.TONE_PROP_BEEP, false)
      copyCode(item.code or "")
    end)

    test_btn.setOnClickListener(function()
      playSound(SOUND_CODE_HIT, nil, ToneGenerator.TONE_PROP_BEEP, false)
      runLuaCodeTestPreview(item.code or "", function(ok, msg)
        showMessage(ok and "Code Test Passed" or "Code Test Error", msg)
      end)
    end)

    details_btn.setOnClickListener(function()
      playSound(SOUND_CODE_HIT, nil, ToneGenerator.TONE_PROP_BEEP, false)
      if item.id then
        local view_url = FIREBASE_URL .. "codes/" .. item.id .. "/views/" .. encodeKey(current_username) .. ".json"
        http_post_or_put(view_url, "PUT", true, function() end)
      end
      showAboutCodeDialog(item)
    end)

    feed_container.addView(card, LinearLayout.LayoutParams(-1, -2))
  end
end

local function filterCodes(query)
  local filtered = {}
  query = trim(query):lower()
  for _, item in ipairs(all_codes_data) do
    local title = tostring(item.title or ""):lower()
    local author = tostring(item.author or ""):lower()
    local desc = tostring(item.desc or ""):lower()
    if query == "" or title:find(query, 1, true) or author:find(query, 1, true) or desc:find(query, 1, true) then
      table.insert(filtered, item)
    end
  end
  renderFeedList(filtered)
end

local function parseAndRenderCodesRaw(raw_str)
  all_codes_data = {}
  if raw_str and raw_str ~= "null" then
    local ok, data = pcall(cjson.decode, raw_str)
    if ok and type(data) == "table" then
      for k, v in pairs(data) do
        if type(v) == "table" then
          v.id = k
          table.insert(all_codes_data, v)
        end
      end
    end
  end

  table.sort(all_codes_data, function(a, b)
    local ta = tostring(a.timestamp_raw or a.timestamp or "")
    local tb = tostring(b.timestamp_raw or b.timestamp or "")
    if ta ~= tb then return ta > tb end
    return tostring(a.id or "") > tostring(b.id or "")
  end)

  renderFeedList(all_codes_data)
end

function loadCodesData()
  local cached_codes = loadOfflineCache("all_codes_feed_cache")
  if cached_codes then
    parseAndRenderCodesRaw(cached_codes)
  end
  if not isNetworkAvailable() then return end
  http_get(FIREBASE_URL .. 'codes.json?orderBy="$key"&limitToLast=60', function(success, response)
    if success and response and response ~= "null" then
      saveOfflineCache("all_codes_feed_cache", response)
      parseAndRenderCodesRaw(response)
    elseif not cached_codes then
      parseAndRenderCodesRaw(nil)
    end
  end)
end

function createHomeFeedView()
  local layout = makeLayout(true, 10)
  local search_input = EditText(activity)
  search_input.setHint("Search Lua codes...")
  layout.addView(search_input)

  local scroll = ScrollView(activity)
  feed_container = makeLayout(true, 10)
  scroll.addView(feed_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1))

  search_input.addTextChangedListener({
    onTextChanged = function(s)
      filterCodes(tostring(s))
    end
  })

  return layout
end

-- ========================================================
-- UPLOAD & EDIT CODE POPUP (WITH LIVE CODE TESTING & ERROR BLOCK)
-- ========================================================

function showUploadOrEditCodeDialog(existing_item)
  local is_edit = (type(existing_item) == "table" and existing_item.id ~= nil)
  local layout = makeLayout(true, 15)

  local title_input = EditText(activity)
  title_input.setHint("Enter Code Title")
  if is_edit then title_input.setText(tostring(existing_item.title or "")) end
  layout.addView(title_input)

  local desc_input = EditText(activity)
  desc_input.setHint("Enter Description")
  if is_edit then desc_input.setText(tostring(existing_item.desc or "")) end
  layout.addView(desc_input)

  local code_input = EditText(activity)
  code_input.setHint("Paste full Lua source code here...")
  code_input.setMinLines(7)
  code_input.setGravity(Gravity.TOP)
  if is_edit then code_input.setText(tostring(existing_item.code or "")) end
  layout.addView(code_input, LinearLayout.LayoutParams(-1, 0, 1))

  local test_before_btn = makeButton("Test Code Before " .. (is_edit and "Update" or "Publish"))
  layout.addView(test_before_btn)

  test_before_btn.setOnClickListener(function()
    runLuaCodeTestPreview(tostring(code_input.getText()), function(ok, msg)
      showMessage(ok and "Test Passed (No Errors)" or "Error Found in Code", msg)
    end)
  end)

  local dialog = AlertDialog.Builder(activity)
    .setTitle(is_edit and "Edit / Update Your Code" or "Upload Open Source Code")
    .setView(layout)
    .setPositiveButton(is_edit and "Update Code" or "Publish", nil)
    .setNegativeButton("Cancel", nil)
    .create()

  dialog.show()

  dialog.getButton(-1).setOnClickListener(View.OnClickListener{
    onClick = function()
      local title = trim(title_input.getText())
      local desc = trim(desc_input.getText())
      local content = trim(code_input.getText())

      if title == "" or content == "" then
        showToast("Please enter both title and code.")
        return
      end

      local test_ok, test_msg = runLuaCodeTestPreview(content, nil)
      if not test_ok then
        showMessage("Cannot Publish Code With Errors", "Please fix this error before uploading:\n\n" .. tostring(test_msg))
        return
      end

      playLimitedSound(SOUND_UPLOAD, 3000)

      if is_edit then
        local target_url = FIREBASE_URL .. "codes/" .. tostring(existing_item.id)
        http_post_or_put(target_url .. "/title.json", "PUT", title, function()
          http_post_or_put(target_url .. "/desc.json", "PUT", desc ~= "" and desc or "No description provided", function()
            http_post_or_put(target_url .. "/code.json", "PUT", content, function(success)
              if success then
                playSound(SOUND_SUCCESS, nil, ToneGenerator.TONE_PROP_ACK, false)
                showToast("Code updated successfully!")
                dialog.dismiss()
                loadCodesData()
                if my_container then loadMyUploadsData() end
              else
                showToast("Update failed. Check network.")
              end
            end)
          end)
        end)
      else
        local payload = {
          title = title,
          desc = desc ~= "" and desc or "No description provided",
          code = content,
          author = current_username,
          timestamp = os.date("%Y-%m-%d %H:%M:%S"),
          timestamp_raw = os.date("%Y%m%d%H%M%S")
        }

        http_post_or_put(FIREBASE_URL .. "codes.json", "POST", payload, function(success)
          if success then
            playSound(SOUND_SUCCESS, nil, ToneGenerator.TONE_PROP_ACK, false)
            showToast("Code uploaded successfully!")
            dialog.dismiss()
            loadCodesData()
            if my_container then loadMyUploadsData() end
          else
            showToast("Upload failed. Check network.")
          end
        end)
      end
    end
  })
end

function showUploadCodeDialog()
  showUploadOrEditCodeDialog(nil)
end

-- ========================================================
-- MY CODES VIEW (EDIT / UPDATE, TEST, VIEW & DELETE)
-- ========================================================

local my_container

local function renderMyUploadsFromRaw(raw_str)
  if not my_container then return end
  my_container.removeAllViews()
  local my_list = {}
  local my_name_norm = trim(current_username):lower()

  if raw_str and raw_str ~= "null" then
    local ok, data = pcall(cjson.decode, raw_str)
    if ok and type(data) == "table" then
      for k, v in pairs(data) do
        if type(v) == "table" then
          local auth_norm = trim(tostring(v.author or "")):lower()
          if auth_norm == my_name_norm then
            v.id = k
            table.insert(my_list, v)
          end
        end
      end
    end
  end

  table.sort(my_list, function(a, b)
    local ta = tostring(a.timestamp_raw or a.timestamp or "")
    local tb = tostring(b.timestamp_raw or b.timestamp or "")
    if ta ~= tb then return ta > tb end
    return tostring(a.id or "") > tostring(b.id or "")
  end)

  if #my_list == 0 then
    my_container.addView(makeText("You have not uploaded any codes yet.", 15))
  else
    for _, v in ipairs(my_list) do
      local card = makeLayout(true, 10)
      card.setBackgroundColor(0xFFFFFFFF)
      card.addView(makeText(v.title or "Untitled", 16))
      card.addView(makeText("Description: " .. (v.desc or ""), 12))
      card.addView(makeText("Date: " .. (v.timestamp or "N/A"), 12))
      card.addView(makeText(formatCodeLikesSummary(v.likes), 12))

      local btn_row = makeLayout(false, 4)
      local view_btn = makeButton("View")
      local edit_btn = makeButton("Edit / Update")
      local del_btn = makeButton("Delete")
      btn_row.addView(view_btn, LinearLayout.LayoutParams(0, -2, 1))
      btn_row.addView(edit_btn, LinearLayout.LayoutParams(0, -2, 1))
      btn_row.addView(del_btn, LinearLayout.LayoutParams(0, -2, 1))
      card.addView(btn_row)

      my_container.addView(card, LinearLayout.LayoutParams(-1, -2))

      view_btn.setOnClickListener(function()
        showAboutCodeDialog(v)
      end)

      edit_btn.setOnClickListener(function()
        showUploadOrEditCodeDialog(v)
      end)

      del_btn.setOnClickListener(function()
        http_delete(FIREBASE_URL .. "codes/" .. tostring(v.id) .. ".json", function(ok)
          if ok then
            showToast("Deleted successfully.")
            loadMyUploadsData()
            loadCodesData()
          else
            showToast("Failed to delete code.")
          end
        end)
      end)
    end
  end
end

function loadMyUploadsData()
  if not my_container then return end
  local cached_codes = loadOfflineCache("all_codes_feed_cache")
  if cached_codes then
    renderMyUploadsFromRaw(cached_codes)
  else
    my_container.removeAllViews()
    my_container.addView(makeText("Loading your uploaded codes...", 14))
  end

  if not isNetworkAvailable() then return end

  http_get(FIREBASE_URL .. "codes.json", function(success, response)
    if success and response and response ~= "null" then
      saveOfflineCache("all_codes_feed_cache", response)
      renderMyUploadsFromRaw(response)
    elseif not cached_codes then
      renderMyUploadsFromRaw(nil)
    end
  end)
end

function createMyUploadsView()
  local layout = makeLayout(true, 12)
  layout.addView(makeText("Your Published Codes", 16))

  local scroll = ScrollView(activity)
  my_container = makeLayout(true, 10)
  scroll.addView(my_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 0, 1))

  return layout
end

-- ========================================================
-- GROUP MANAGEMENT DIALOG
-- ========================================================

local function showGroupManagementDialog()
  if not isVerifiedUser(current_username) then
    showToast("Only verified users can manage and ban groups.")
    return
  end

  local layout = makeLayout(true, 12)
  local scroll = ScrollView(activity)
  local container = makeLayout(true, 8)
  scroll.addView(container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 520))

  container.addView(makeText("Loading all registered groups...", 14))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Group Management (Verified)")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()
  dialog.show()

  local function loadManageableGroups()
    http_get(FIREBASE_URL .. "btp_groups.json", function(s, r)
      container.removeAllViews()
      if not s or not r or r == "null" then
        container.addView(makeText("No groups found.", 14))
        return
      end
      local ok, data = pcall(cjson.decode, r)
      if not ok or type(data) ~= "table" then
        container.addView(makeText("No groups found.", 14))
        return
      end

      local list = {}
      for gid, g in pairs(data) do
        if type(g) == "table" then
          g.id = gid
          table.insert(list, g)
        end
      end

      table.sort(list, function(a, b)
        return tostring(a.name or ""):lower() < tostring(b.name or ""):lower()
      end)

      if #list == 0 then
        container.addView(makeText("No groups found.", 14))
        return
      end

      for _, g in ipairs(list) do
        local is_b = (g.is_banned == true or g.is_banned == "true")
        local card = makeLayout(true, 10)
        card.setBackgroundColor(is_b and 0xFFFFCDD2 or 0xFFEEEEEE)
        card.addView(makeText(tostring(g.name or "Unnamed") .. (is_b and " [BANNED]" or " [ACTIVE]"), 15))
        card.addView(makeText("Creator: " .. getVerifiedName(g.creator or "") .. " • Members: " .. tostring(g.members and table_size(g.members) or 1), 12))

        local act_row = makeLayout(false, 4)
        local toggle_ban_btn = makeButton(is_b and "Unban Group" or "Ban Group")
        local delete_grp_btn = makeButton("Delete Group")
        delete_grp_btn.setBackgroundColor(0xFFD32F2F)
        delete_grp_btn.setTextColor(0xFFFFFFFF)
        act_row.addView(toggle_ban_btn, LinearLayout.LayoutParams(0, -2, 1))
        act_row.addView(delete_grp_btn, LinearLayout.LayoutParams(0, -2, 1))
        card.addView(act_row, LinearLayout.LayoutParams(-1, -2))
        container.addView(card, LinearLayout.LayoutParams(-1, -2))

        toggle_ban_btn.setOnClickListener(function()
          local next_b = not is_b
          http_post_or_put(FIREBASE_URL .. "btp_groups/" .. g.id .. "/is_banned.json", "PUT", next_b, function(ok)
            if ok then
              showToast(next_b and ("Banned group: " .. tostring(g.name or "")) or ("Unbanned group: " .. tostring(g.name or "")))
              loadManageableGroups()
            end
          end)
        end)

        delete_grp_btn.setOnClickListener(function()
          http_delete(FIREBASE_URL .. "btp_groups/" .. g.id .. ".json", function()
            http_delete(FIREBASE_URL .. "btp_group_messages/" .. g.id .. ".json", function() end)
            showToast("Deleted group: " .. tostring(g.name or ""))
            loadManageableGroups()
          end)
        end)
      end
    end)
  end

  loadManageableGroups()
end

-- ========================================================
-- ADMIN PANEL DIALOG (WITH SEND YOUTUBE LINK FEATURE)
-- ========================================================

function showAdminPanelDialog()
  local full_access = isVerifiedUser(current_username)
  local layout = makeLayout(true, 15)

  local broadcast_btn = makeButton("Send Notification Broadcast")
  layout.addView(broadcast_btn)

  broadcast_btn.setOnClickListener(function()
    local input = EditText(activity)
    input.setHint("Write announcement message...")

    AlertDialog.Builder(activity)
      .setTitle("Broadcast to Notifications")
      .setView(input)
      .setPositiveButton("Send", DialogInterface.OnClickListener{
        onClick = function()
          local msg = trim(input.getText())
          if msg ~= "" then
            http_post_or_put(FIREBASE_URL .. "settings/broadcast.json", "PUT", msg, function(ok)
              if ok then
                playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP2, false)
                showToast("Broadcast sent!")
              end
            end)
          end
        end
      })
      .setNegativeButton("Clear Broadcast", DialogInterface.OnClickListener{
        onClick = function()
          http_delete(FIREBASE_URL .. "settings/broadcast.json", function()
            showToast("Broadcast cleared.")
          end)
        end
      })
      .show()
  end)

  if full_access then
    local send_yt_btn = makeButton("Send YouTube Link")
    local assistant_mgmt_btn = makeButton("Assistant Management (Lock, Train & Feedback)")
    local group_mgmt_btn = makeButton("Group Management (Ban / Unban / Delete)")
    local lock_room_btn = makeButton(public_room_locked and "Unlock BTP Voice Room (Currently Locked)" or "Lock BTP Voice Room (Only Admin/Dev)")
    local server_toggle_btn = makeButton(server_is_down and "Turn Server ON (Currently Server OFF)" or "Turn Server OFF (Maintenance Mode)")
    local popup_note_btn = makeButton("Update Popup Announcement Note")
    local users_mgmt_btn = makeButton("Manage Users (Role, Admin, Verified & Block)")
    local blocked_users_btn = makeButton("View Blocked Users & Unblock Requests")

    layout.addView(send_yt_btn)
    layout.addView(assistant_mgmt_btn)
    layout.addView(group_mgmt_btn)
    layout.addView(lock_room_btn)
    layout.addView(server_toggle_btn)
    layout.addView(popup_note_btn)
    layout.addView(users_mgmt_btn)
    layout.addView(blocked_users_btn)

    send_yt_btn.setOnClickListener(function()
      local yt_box = makeLayout(true, 14)
      local yt_title_inp = EditText(activity)
      yt_title_inp.setHint("Enter Video Title")
      local yt_link_inp = EditText(activity)
      yt_link_inp.setHint("Paste YouTube Link (https://youtu.be/...)")

      yt_box.addView(yt_title_inp)
      yt_box.addView(yt_link_inp)

      AlertDialog.Builder(activity)
        .setTitle("Send YouTube Link to All Users")
        .setView(yt_box)
        .setPositiveButton("Publish", DialogInterface.OnClickListener{
          onClick = function()
            local v_title = trim(yt_title_inp.getText())
            local v_link = trim(yt_link_inp.getText())
            if v_title == "" or v_link == "" then
              showToast("Please enter both Video Title and YouTube Link.")
              return
            end
            local yt_payload = {
              yt_id = "yt_" .. tostring(os.time()),
              title = v_title,
              url = v_link,
              posted_by = current_username,
              timestamp = os.date("%I:%M %p, %d %b %Y")
            }
            http_post_or_put(FIREBASE_URL .. "settings/youtube_broadcast.json", "PUT", yt_payload, function(ok)
              if ok then
                playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP2, false)
                showToast("YouTube link published to all users!")
              else
                showToast("Failed to publish YouTube link.")
              end
            end)
          end
        })
        .setNegativeButton("Clear Link", DialogInterface.OnClickListener{
          onClick = function()
            http_delete(FIREBASE_URL .. "settings/youtube_broadcast.json", function()
              showToast("YouTube link broadcast cleared.")
            end)
          end
        })
        .show()
    end)

    assistant_mgmt_btn.setOnClickListener(function()
      showAssistantManagementDialog()
    end)

    group_mgmt_btn.setOnClickListener(function()
      showGroupManagementDialog()
    end)

    lock_room_btn.setOnClickListener(function()
      local next_lock = not public_room_locked
      http_post_or_put(FIREBASE_URL .. "settings/public_room_locked.json", "PUT", next_lock, function(ok)
        if ok then
          public_room_locked = next_lock
          lock_room_btn.setText(public_room_locked and "Unlock BTP Voice Room (Currently Locked)" or "Lock BTP Voice Room (Only Admin/Dev)")
          showToast(public_room_locked and "BTP Voice Room locked." or "BTP Voice Room unlocked.")
        end
      end)
    end)

    server_toggle_btn.setOnClickListener(function()
      local next_down = not server_is_down
      http_post_or_put(FIREBASE_URL .. "settings/server_down.json", "PUT", next_down, function(ok)
        if ok then
          server_is_down = next_down
          server_toggle_btn.setText(server_is_down and "Turn Server ON (Currently Server OFF)" or "Turn Server OFF (Maintenance Mode)")
          showToast(server_is_down and "Server is now OFF for users." or "Server is now ON.")
        end
      end)
    end)

    popup_note_btn.setOnClickListener(function()
      local note_layout = makeLayout(true, 15)
      local note_input = EditText(activity)
      note_input.setHint("Write popup announcement note for all users...")
      note_input.setMinLines(4)
      note_input.setGravity(Gravity.TOP)
      note_layout.addView(note_input)

      http_get(FIREBASE_URL .. "settings/popup_announcement.json", function(s, r)
        if s and r and r ~= "null" then
          local ok, data = pcall(cjson.decode, r)
          if ok and type(data) == "table" and data.message then
            note_input.setText(tostring(data.message))
          elseif ok and type(data) == "string" then
            note_input.setText(data)
          end
        end
      end)

      AlertDialog.Builder(activity)
        .setTitle("Popup Announcement Note")
        .setView(note_layout)
        .setPositiveButton("Publish Note", DialogInterface.OnClickListener{
          onClick = function()
            local msg = trim(note_input.getText())
            if msg ~= "" then
              local payload = {
                note_id = "note_" .. tostring(os.time()),
                message = msg,
                timestamp = os.date("%I:%M %p, %d %b %Y")
              }
              http_post_or_put(FIREBASE_URL .. "settings/popup_announcement.json", "PUT", payload, function(ok)
                if ok then
                  playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP2, false)
                  showToast("Popup announcement note published!")
                end
              end)
            else
              showToast("Please write a note first.")
            end
          end
        })
        .setNegativeButton("Clear Note", DialogInterface.OnClickListener{
          onClick = function()
            http_delete(FIREBASE_URL .. "settings/popup_announcement.json", function()
              showToast("Popup announcement note cleared.")
            end)
          end
        })
        .show()
    end)

    users_mgmt_btn.setOnClickListener(function()
      local u_layout = makeLayout(true, 10)
      local u_scroll = ScrollView(activity)
      local u_container = makeLayout(true, 8)
      u_scroll.addView(u_container)
      u_layout.addView(u_scroll, LinearLayout.LayoutParams(-1, 520))

      u_container.addView(makeText("Loading users in alphabetical order...", 14))

      local u_dialog = AlertDialog.Builder(activity)
        .setTitle("Registered Users (A-Z)")
        .setView(u_layout)
        .setPositiveButton("Close", nil)
        .create()

      u_dialog.show()

      http_get(FIREBASE_URL .. "registered_users.json", function(s, r)
        loadVerifiedUsers(function()
          loadAdminUsers(function()
            loadBlockedUsers(function()
              u_container.removeAllViews()
              local all_names = {}

              if s and r and r ~= "null" then
                local ok, data = pcall(cjson.decode, r)
                if ok and type(data) == "table" then
                  for uname, uinfo in pairs(data) do
                    local actual_name = (type(uinfo) == "table" and uinfo.username) or uname
                    if actual_name and actual_name ~= "" then
                      table.insert(all_names, actual_name)
                    end
                  end
                end
              end

              local has_ibrahim = false
              for _, n in ipairs(all_names) do
                if n:lower() == "ibrahim ansari" then has_ibrahim = true break end
              end
              if not has_ibrahim then table.insert(all_names, "Ibrahim Ansari") end

              table.sort(all_names, function(a, b)
                return tostring(a):lower() < tostring(b):lower()
              end)

              if #all_names == 0 then
                u_container.addView(makeText("No registered users found.", 14))
              else
                local current_alphabet = ""
                for _, actual_name in ipairs(all_names) do
                  local first_char = tostring(actual_name:sub(1, 1)):upper()
                  if first_char ~= current_alphabet then
                    current_alphabet = first_char
                    local section_header = makeText("── Section " .. current_alphabet .. " ──", 14)
                    section_header.setTextColor(0xFF1E88E5)
                    section_header.setPadding(0, 10, 0, 4)
                    u_container.addView(section_header)
                  end

                  local is_ver = isVerifiedUser(actual_name)
                  local is_adm = isAdminUser(actual_name)
                  local is_blocked = (blocked_users_map[actual_name] == true or blocked_users_map[actual_name] == "true")

                  local row = makeLayout(true, 8)
                  row.setBackgroundColor(is_blocked and 0xFFFFCDD2 or 0xFFEEEEEE)
                  row.addView(makeText("User: " .. getRoleBadgeText(actual_name), 15))

                  local role_label = is_ver and "Verified" or (is_adm and "Admin" or "Normal")
                  local status_str = "Role: " .. role_label .. " • " .. (is_blocked and "BLOCKED" or "Active")
                  row.addView(makeText(status_str, 12))

                  local action_row = makeLayout(false, 4)
                  local toggle_admin_btn = makeButton(is_adm and "Remove Admin" or "Make Admin")
                  local toggle_verify_btn = makeButton(is_ver and "Remove Verified" or "Make Verified")
                  local toggle_block_btn = makeButton(is_blocked and "Unblock" or "Block User")

                  action_row.addView(toggle_admin_btn, LinearLayout.LayoutParams(0, -2, 1))
                  action_row.addView(toggle_verify_btn, LinearLayout.LayoutParams(0, -2, 1))
                  action_row.addView(toggle_block_btn, LinearLayout.LayoutParams(0, -2, 1))
                  row.addView(action_row)

                  u_container.addView(row, LinearLayout.LayoutParams(-1, -2))

                  toggle_admin_btn.setOnClickListener(function()
                    if is_adm then
                      http_delete(FIREBASE_URL .. "admin_users/" .. encodeKey(actual_name) .. ".json", function()
                        showToast(actual_name .. " removed from Admin.")
                        u_dialog.dismiss()
                        loadAdminUsers()
                      end)
                    else
                      http_post_or_put(FIREBASE_URL .. "admin_users/" .. encodeKey(actual_name) .. ".json", "PUT", true, function()
                        showToast(actual_name .. " is now Admin!")
                        u_dialog.dismiss()
                        loadAdminUsers()
                      end)
                    end
                  end)

                  toggle_verify_btn.setOnClickListener(function()
                    if is_ver then
                      if isDeveloper(actual_name) then
                        showToast("Developer cannot be unverified.")
                        return
                      end
                      http_delete(FIREBASE_URL .. "verified_users/" .. encodeKey(actual_name) .. ".json", function()
                        showToast(actual_name .. " is now unverified.")
                        u_dialog.dismiss()
                        loadVerifiedUsers()
                      end)
                    else
                      http_post_or_put(FIREBASE_URL .. "verified_users/" .. encodeKey(actual_name) .. ".json", "PUT", true, function()
                        showToast(actual_name .. " is now Verified!")
                        u_dialog.dismiss()
                        loadVerifiedUsers()
                      end)
                    end
                  end)

                  toggle_block_btn.setOnClickListener(function()
                    if is_blocked then
                      http_delete(FIREBASE_URL .. "blocked/" .. encodeKey(actual_name) .. ".json", function()
                        http_delete(FIREBASE_URL .. "unblock_requests/" .. encodeKey(actual_name) .. ".json", function() end)
                        showToast(actual_name .. " unblocked.")
                        u_dialog.dismiss()
                        loadBlockedUsers()
                      end)
                    else
                      if isDeveloper(actual_name) then
                        showToast("Developer cannot be blocked!")
                        return
                      end
                      http_post_or_put(FIREBASE_URL .. "blocked/" .. encodeKey(actual_name) .. ".json", "PUT", true, function()
                        showToast(actual_name .. " has been blocked.")
                        u_dialog.dismiss()
                        loadBlockedUsers()
                      end)
                    end
                  end)
                end
              end
            end)
          end)
        end)
      end)
    end)

    blocked_users_btn.setOnClickListener(function()
      local b_layout = makeLayout(true, 10)
      local b_scroll = ScrollView(activity)
      local b_container = makeLayout(true, 8)
      b_scroll.addView(b_container)
      b_layout.addView(b_scroll, LinearLayout.LayoutParams(-1, 500))

      b_container.addView(makeText("Loading blocked users & unblock requests...", 14))

      local b_dialog = AlertDialog.Builder(activity)
        .setTitle("Blocked Users & Requests")
        .setView(b_layout)
        .setPositiveButton("Close", nil)
        .create()

      b_dialog.show()

      http_get(FIREBASE_URL .. "blocked.json", function(s, r)
        http_get(FIREBASE_URL .. "unblock_requests.json", function(s_req, r_req)
          b_container.removeAllViews()
          local requests_map = {}
          if s_req and r_req and r_req ~= "null" then
            local ok, req_data = pcall(cjson.decode, r_req)
            if ok and type(req_data) == "table" then requests_map = req_data end
          end

          local count_blocked = 0
          if s and r and r ~= "null" then
            local ok, data = pcall(cjson.decode, r)
            if ok and type(data) == "table" then
              for buname, is_blk in pairs(data) do
                if is_blk == true or is_blk == "true" then
                  count_blocked = count_blocked + 1
                  local card = makeLayout(true, 8)
                  card.setBackgroundColor(0xFFEEEEEE)
                  card.addView(makeText("Blocked User: " .. buname, 15))

                  if requests_map[buname] then
                    local r_info = requests_map[buname]
                    local req_msg = type(r_info) == "table" and r_info.message or "Requesting unblock"
                    card.addView(makeText("Unblock Request: " .. req_msg, 12))
                  end

                  local unblock_btn = makeButton("Unblock " .. buname)
                  card.addView(unblock_btn)
                  b_container.addView(card, LinearLayout.LayoutParams(-1, -2))

                  unblock_btn.setOnClickListener(function()
                    http_delete(FIREBASE_URL .. "blocked/" .. encodeKey(buname) .. ".json", function()
                      http_delete(FIREBASE_URL .. "unblock_requests/" .. encodeKey(buname) .. ".json", function() end)
                      showToast(buname .. " has been unblocked.")
                      b_dialog.dismiss()
                      loadBlockedUsers()
                    end)
                  end)
                end
              end
            end
          end

          if count_blocked == 0 then
            b_container.addView(makeText("No blocked users.", 14))
          end
        end)
      end)
    end)
  end

  AlertDialog.Builder(activity)
    .setTitle(full_access and "Admin Panel (Verified / Developer)" or "Admin Panel (Notification Only)")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .show()
end

-- ========================================================
-- NOTIFICATION & PRIVACY SETTINGS POPUP
-- ========================================================

function showNotificationPrivacyDialog()
  local layout = makeLayout(true, 18)

  local notif_sound_status = sp.getBoolean("notif_sound_enabled", false)
  local share_presence_status = sp.getBoolean("share_presence_enabled", true)

  local notif_toggle_btn = makeButton("Notifications Sound (In-App): " .. (notif_sound_status and "ENABLED ON" or "DISABLED OFF"))
  local presence_toggle_btn = makeButton("Show Online / Last Seen: " .. (share_presence_status and "VISIBLE ON" or "HIDDEN OFF"))

  layout.addView(makeText("Configure sound alerts and online visibility:", 13))
  layout.addView(notif_toggle_btn)
  layout.addView(presence_toggle_btn)

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Notification & Privacy Settings")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()

  dialog.show()

  notif_toggle_btn.setOnClickListener(function()
    local current = sp.getBoolean("notif_sound_enabled", false)
    local new_val = not current
    sp.edit().putBoolean("notif_sound_enabled", new_val).apply()
    notif_toggle_btn.setText("Notifications Sound (In-App): " .. (new_val and "ENABLED ON" or "DISABLED OFF"))
    if new_val then
      startBackgroundNotificationWatcher()
      showToast("Notification alerts enabled.")
    else
      stopBackgroundNotificationWatcher()
      showToast("Notification alerts turned off.")
    end
  end)

  presence_toggle_btn.setOnClickListener(function()
    local current = sp.getBoolean("share_presence_enabled", true)
    local new_val = not current
    sp.edit().putBoolean("share_presence_enabled", new_val).apply()
    presence_toggle_btn.setText("Show Online / Last Seen: " .. (new_val and "VISIBLE ON" or "HIDDEN OFF"))
    if not new_val then
      http_delete(FIREBASE_URL .. "user_presence/" .. encodeKey(current_username) .. ".json", function() end)
      showToast("Online status hidden from other users.")
    else
      updatePresence("online")
      showToast("Online status is now visible.")
    end
  end)
end

-- ========================================================
-- SETTINGS VIEW (MORE OPTIONS: PERSONAL ASSISTANT + GROUPS)
-- ========================================================

function createSettingsView()
  local layout = makeLayout(true, 20)
  CURRENT_VERSION = getCurrentAppVersion()

  local check_update_btn = makeButton("Check for Update (Current: " .. CURRENT_VERSION .. ")")
  check_update_btn.setContentDescription("Check for Update")
  layout.addView(check_update_btn)

  check_update_btn.setOnClickListener(function()
    checkUpdate(true)
  end)

  local change_name = makeButton("Change Username")
  layout.addView(change_name)

  local more_options_btn = makeButton("More Options (BTP Assistant Auto-Reply & Groups)")
  layout.addView(more_options_btn)

  more_options_btn.setOnClickListener(function()
    local opts = {
      "Personal Chat BTP Assistant (ON / OFF & Train)",
      "Create New Group",
      "View All Groups"
    }
    AlertDialog.Builder(activity)
      .setTitle("More Options")
      .setItems(opts, DialogInterface.OnClickListener{
        onClick = function(d, w)
          if w == 0 then
            showPersonalAssistantSetupDialog()
          elseif w == 1 then
            showCreateGroupDialog(function()
              showGroupsListDialog()
            end)
          else
            showGroupsListDialog()
          end
        end
      }).show()
  end)

  local notif_privacy_btn = makeButton("Notification & Privacy Settings")
  layout.addView(notif_privacy_btn)

  notif_privacy_btn.setOnClickListener(function()
    showNotificationPrivacyDialog()
  end)

  local admin_panel_container = makeLayout(true, 0)
  layout.addView(admin_panel_container)

  loadVerifiedUsers(function()
    loadAdminUsers(function()
      syncServerAndRoomSettings(function()
        local is_ver = isVerifiedUser(current_username)
        local is_adm = isAdminUser(current_username)
        if is_ver or is_adm then
          admin_panel_container.removeAllViews()
          local btn_label = is_ver and "Admin Panel (Verified / Developer)" or "Admin Panel (Admin)"
          local admin_panel_btn = makeButton(btn_label)
          admin_panel_btn.setBackgroundColor(0xFF2E7D32)
          admin_panel_btn.setTextColor(0xFFFFFFFF)
          admin_panel_container.addView(admin_panel_btn)

          admin_panel_btn.setOnClickListener(function()
            showAdminPanelDialog()
          end)
        end
      end)
    end)
  end)

  local about_app = makeButton("About Application")
  layout.addView(about_app)

  local feedback = makeButton("Send Feedback via WhatsApp")
  layout.addView(feedback)

  change_name.setOnClickListener(function()
    local input = EditText(activity)
    input.setText(current_username)
    AlertDialog.Builder(activity)
      .setTitle("Change Username")
      .setView(input)
      .setPositiveButton("Save", DialogInterface.OnClickListener{
        onClick = function()
          local name = trim(input.getText())
          if name ~= "" then
            sp.edit().putString("username", name).apply()
            current_username = name
            registerUserToFirebase(name)
            updatePresence("online")
            showToast("Username updated.")
            initMainWindow()
          end
        end
      })
      .setNegativeButton("Cancel", nil)
      .show()
  end)

  about_app.setOnClickListener(function()
    CURRENT_VERSION = getCurrentAppVersion()
    showMessage(
      "About This App",
      APP_TITLE .. "\n" .. APP_DEV .. "\nVersion: " .. CURRENT_VERSION .. "\n\n"
      .. "A fast, accessible community and code-sharing hub built for creators and developers. "
      .. "Includes BTP Assistant for smart Q&A, personal offline auto-replies, BTP Voice Room, community groups, "
      .. "direct chats with real-time live voice calls, and clean screen-reader support."
    )
  end)

  feedback.setOnClickListener(function()
    local url = "https://api.whatsapp.com/send?phone=917481878723&text=" .. Uri.encode("Feedback for " .. APP_TITLE)
    local intent = Intent(Intent.ACTION_VIEW)
    intent.setData(Uri.parse(url))
    pcall(function() activity.startActivity(intent) end)
  end)

  return layout
end

-- ========================================================
-- MAIN APPLICATION WINDOW
-- ========================================================

function initMainWindow()
  local root = makeLayout(true, 0)
  root.setBackgroundColor(0xFFF5F5F5)

  local header = makeLayout(true, 14)
  header.setBackgroundColor(0xFF1E88E5)

  local title = makeText(APP_TITLE, 18)
  title.setTextColor(0xFFFFFFFF)
  header.addView(title)

  local dev_label = makeText(APP_DEV, 13)
  dev_label.setTextColor(0xFFE3F2FD)
  header.addView(dev_label)

  local user_label = makeText("User: " .. getVerifiedName(current_username), 13)
  user_label.setTextColor(0xFFFFF176)
  header.addView(user_label)

  notif_button = makeButton("Notifications")
  notif_button.setOnClickListener(function() showNotificationsDialog() end)
  header.addView(notif_button, LinearLayout.LayoutParams(-1, -2))
  root.addView(header)

  local nav_bar = makeLayout(false, 2)
  nav_bar.setBackgroundColor(0xFFE0E0E0)

  local home_btn = makeButton("Home")
  chat_tab_btn = makeButton("Chat")
  local upload_btn = makeButton("Upload Code")
  local my_codes_btn = makeButton("My Codes")
  local settings_btn = makeButton("Settings")

  local nav_params = LinearLayout.LayoutParams(0, -2, 1)
  nav_bar.addView(home_btn, nav_params)
  nav_bar.addView(chat_tab_btn, nav_params)
  nav_bar.addView(upload_btn, nav_params)
  nav_bar.addView(my_codes_btn, nav_params)
  nav_bar.addView(settings_btn, nav_params)
  root.addView(nav_bar)

  main_content = FrameLayout(activity)
  root.addView(main_content, LinearLayout.LayoutParams(-1, 0, 1))

  activity.setContentView(root)

  local home_view = createHomeFeedView()
  local my_view = createMyUploadsView()

  local function showOnlyView(view)
    main_content.removeAllViews()
    main_content.addView(view)
  end

  home_btn.setOnClickListener(function()
    showOnlyView(home_view)
    loadCodesData()
  end)

  chat_tab_btn.setOnClickListener(function()
    showResourceChatDialog()
  end)

  upload_btn.setOnClickListener(function()
    showUploadCodeDialog()
  end)

  my_codes_btn.setOnClickListener(function()
    showOnlyView(my_view)
    loadMyUploadsData()
  end)

  settings_btn.setOnClickListener(function()
    local settings_view = createSettingsView()
    showOnlyView(settings_view)
  end)

  showOnlyView(home_view)
  loadCodesData()
  updateNotificationCount(true)

  if sp.getBoolean("notif_sound_enabled", false) then
    startBackgroundNotificationWatcher()
  end
end

-- ========================================================
-- LIFECYCLE HOOKS: ZERO BACKGROUND NETWORK/DATA USAGE
-- ========================================================

function onPause()
  isAppForeground = false
  stopBackgroundNotificationWatcher()
  stopIncomingCallWatcher()
  stopPresenceTracking()
end

function onResume()
  isAppForeground = true
  if current_username ~= "" then
    startPresenceTracking()
    startIncomingCallWatcher()
    if sp.getBoolean("notif_sound_enabled", false) then
      startBackgroundNotificationWatcher()
    end
  end
end

function onStop()
  isAppForeground = false
  stopActiveVoicePlayer(false)
  stopBackgroundNotificationWatcher()
  stopIncomingCallWatcher()
  stopPresenceTracking()
  resetCallAudioMode()
end

function onDestroy()
  isAppForeground = false
  stopActiveVoicePlayer(false)
  stopBackgroundNotificationWatcher()
  stopIncomingCallWatcher()
  stopPresenceTracking()
  resetCallAudioMode()
  updatePresence("offline")
end

-- ========================================================
-- STARTUP SEQUENCE
-- ========================================================

if current_username == "" then
  showWelcomeDialog()
else
  initMainWindow()

  registerUserToFirebase(current_username)
  startPresenceTracking()
  startIncomingCallWatcher()

  loadVerifiedUsers(function()
    loadAdminUsers(function()
      syncServerAndRoomSettings(function()
        loadBlockedUsers(function()
          checkBlockStatus(function()
            checkPopupAnnouncementNote()
          end)
        end)
      end)
    end)
  end)

  Handler(Looper.getMainLooper()).postDelayed(Runnable({
    run = function()
      checkUpdate(false)
    end
  }), 3000)

  local cleanup_handler = Handler(Looper.getMainLooper())
  cleanup_handler.postDelayed(Runnable({
    run = function()
      runSilentAutoCleanup()
    end
  }), 15000)
end