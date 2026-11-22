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

local APP_TITLE = "All Open Source by Blind Tech Power Hub"
local APP_DEV = "Developer: Ibrahim Ansari"
local APP_VERSION = "1.0"
local FIREBASE_URL = "https://ibrahim-6e4a3-default-rtdb.firebaseio.com/"

local MAX_VOICE_SECONDS = 45
local CHAT_POLL_INTERVAL_MS = 8000
local ROOM_POLL_INTERVAL_MS = 8000
local CALL_POLL_INTERVAL_MS = 2500
local CALL_RING_TIMEOUT_SEC = 35
local DISAPPEAR_24H_SEC = 86400

local sp = activity.getSharedPreferences("BTP_USER_PREFS", Context.MODE_PRIVATE)
local current_username = tostring(sp.getString("username", ""))

local all_codes_data = {}
local main_content
local notif_button
local chat_tab_btn
local verified_users_map = {}
local admin_users_map = {}
local blocked_users_map = {}
local presence_handler = nil
local presence_runnable = nil

-- Server, Room & Assistant Control State
local server_is_down = false
local public_room_locked = false
local assistant_is_locked = false
local assistant_trained_items = {}

-- Incoming Call / Live Voice Chat Watcher State
local incoming_call_handler = nil
local incoming_call_runnable = nil
local active_call_dialog = nil
local active_call_id = nil
local active_call_is_muted = false
local active_call_speaker_on = true
local active_voice_chat_dialog = nil
local active_voice_chat_id = nil

-- Global Sound & Notification Trackers
local bg_notif_handler = nil
local bg_notif_runnable = nil
local known_code_ids = {}
local known_notif_keys = {}
local known_bg_msg_ids = {}
local known_reaction_keys = {}
local is_first_bg_sync_done = false
local last_sound_play_time = 0

-- Active Voice Player, Queue & SeekBar Trackers
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
-- SOUND PATHS & ENCRYPTION-SAFE MEDIA / TONE HELPERS
-- ========================================================

local SOUND_BASE_DIR = "/storage/emulated/0/解说/Tools/all open source by blind Tech power hub. /allopensourcebyblindTechpowerhub/"
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
  if ok then return res else return true end
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
  return tostring(s or ""):match("^%s*(.-)%s*$")
end

-- ========================================================
-- CORE UI BUILDERS (DEFINED FIRST TO PREVENT NIL ERRORS)
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
-- AUTO UPDATE SYSTEM (VERSION TRACKED, NO REPEATED POPUP, MANUAL CHECK)
-- ========================================================

local UPDATE_CURRENT_VERSION = APP_VERSION
local UPDATE_VERSION_URL = "https://raw.githubusercontent.com/blindpowerhub-hash/ibrahim/main/virgin.txt"
local UPDATE_CODE_URL = "https://raw.githubusercontent.com/blindpowerhub-hash/ibrahim/main/main.lua"
local UPDATE_PLUGIN_PATH = (function()
  local ok, p = pcall(function()
    local src = debug.getinfo(1, "S").source
    return src and src:match("^@?(.*)$") or ""
  end)
  return (ok and p) or ""
end)()
local updateInProgress = false
local updatePrefs = activity.getSharedPreferences("AutoUpdatePrefs", Context.MODE_PRIVATE)

local function playUpdateCue()
  pcall(function()
    local tone = ToneGenerator(AudioManager.STREAM_NOTIFICATION, 100)
    tone.startTone(ToneGenerator.TONE_PROP_ACK, 120)
    local vibrator = activity.getSystemService(Context.VIBRATOR_SERVICE)
    if vibrator then
      if Build.VERSION.SDK_INT >= 26 then
        vibrator.vibrate(VibrationEffect.createOneShot(180, VibrationEffect.DEFAULT_AMPLITUDE))
      else
        vibrator.vibrate(180)
      end
    end
  end)
end

local function showUpdateErrorDialog(title, message)
  Handler(Looper.getMainLooper()).post(Runnable({
    run = function()
      local errorDialog = LuaDialog(activity)
      errorDialog.setTitle(title)
      errorDialog.setMessage(message)
      errorDialog.setButton("OK", function()
        errorDialog.dismiss()
      end)
      errorDialog.show()
    end
  }))
end

local function isValidVersionString(v)
  local s = trim(tostring(v or ""))
  if s == "" or #s > 16 then return false end
  if s:lower():find("404", 1, true) or s:lower():find("html", 1, true) then return false end
  return s:match("^[%w%.%-_]+$") ~= nil
end

local function performPluginUpdate(mainCode, onlineVersion)
  if not mainCode or trim(mainCode) == "" then
    showUpdateErrorDialog("Update Failed", "Updated script code is empty.")
    return
  end

  if UPDATE_PLUGIN_PATH == "" or not File(UPDATE_PLUGIN_PATH).exists() then
    showUpdateErrorDialog("Update Ready", "Latest version " .. tostring(onlineVersion) .. " downloaded. Please replace your script file manually if running from an unsaved buffer.")
    return
  end

  updateInProgress = true

  local function updateProcess()
    local success = false
    local tempPath = UPDATE_PLUGIN_PATH .. ".temp_update"
    local f = io.open(tempPath, "w")
    if f then
      f:write(mainCode)
      f:close()

      local delOk = pcall(function() os.remove(UPDATE_PLUGIN_PATH) end)
      if delOk then
        local renOk = pcall(function() os.rename(tempPath, UPDATE_PLUGIN_PATH) end)
        if renOk then
          success = true
        end
      end

      if not success then
        pcall(function() os.remove(tempPath) end)
      end
    end

    if success then
      updateInProgress = false
      updatePrefs.edit()
        .putString("lastPromptedVersion", "")
        .putString("installedVersion", tostring(onlineVersion))
        .apply()

      Handler(Looper.getMainLooper()).post(Runnable({
        run = function()
          playUpdateCue()
          local successDialog = LuaDialog(activity)
          successDialog.setTitle("Update Successful")
          successDialog.setMessage("Updated to version " .. tostring(onlineVersion) .. ".\n\nTap OK to reload and apply the update.")
          successDialog.setButton("OK", function()
            successDialog.dismiss()
            Handler(Looper.getMainLooper()).postDelayed(Runnable({
              run = function()
                local func, err = loadfile(UPDATE_PLUGIN_PATH)
                if func then
                  pcall(func)
                else
                  showToast("Error reloading script: " .. tostring(err))
                end
              end
            }), 600)
          end)
          successDialog.show()
        end
      }))
    else
      updateInProgress = false
      showUpdateErrorDialog("Update Failed", "Unable to write updated script file. Please try again.")
    end
  end

  Thread(Runnable{ run = updateProcess }).start()
end

local function promptForVersionUpdate(onlineVersion, mainCode)
  Handler(Looper.getMainLooper()).post(Runnable({
    run = function()
      playUpdateCue()
      local updateAlertDlg = LuaDialog(activity)
      updateAlertDlg.setTitle("Update Available")
      updateAlertDlg.setMessage("A new version (" .. tostring(onlineVersion) .. ") is available.\nCurrent version: " .. tostring(UPDATE_CURRENT_VERSION) .. "\n\nWould you like to update now?")
      updateAlertDlg.setButton("Update Now", function()
        updateAlertDlg.dismiss()
        showToast("Downloading update...")
        performPluginUpdate(mainCode, onlineVersion)
      end)
      updateAlertDlg.setButton2("Later", function()
        updatePrefs.edit().putString("lastPromptedVersion", tostring(onlineVersion)).apply()
        updateAlertDlg.dismiss()
      end)
      updateAlertDlg.show()
    end
  }))
end

function checkForAppUpdate(isManualCheck)
  if updateInProgress then
    if isManualCheck then showToast("Update already in progress.") end
    return
  end
  if not isNetworkAvailable() then
    if isManualCheck then showToast("No internet connection.") end
    return
  end

  local timestamp = tostring(System.currentTimeMillis())
  Http.get(UPDATE_VERSION_URL .. "?t=" .. timestamp, function(code, response)
    if code == 200 and response then
      local onlineVersion = trim(response)
      if not isValidVersionString(onlineVersion) then
        if isManualCheck then showToast("Up to date, you are using latest version.") end
        return
      end

      if onlineVersion == UPDATE_CURRENT_VERSION then
        if isManualCheck then
          showMessage("Check for Update", "Up to date, you are using latest version (" .. UPDATE_CURRENT_VERSION .. ").")
        end
        return
      end

      local lastPrompted = tostring(updatePrefs.getString("lastPromptedVersion", ""))
      if (not isManualCheck) and lastPrompted == onlineVersion then
        return
      end

      Http.get(UPDATE_CODE_URL .. "?t=" .. timestamp, function(code2, mainCode)
        if code2 == 200 and mainCode and trim(mainCode) ~= "" then
          promptForVersionUpdate(onlineVersion, mainCode)
        elseif isManualCheck then
          showToast("Unable to download update package right now.")
        end
      end)
    elseif isManualCheck then
      showToast("Up to date, you are using latest version.")
    end
  end)
end

-- ========================================================
-- SERVER STATUS & ROLE HELPERS (EXACT VERIFIED IDs + ADMIN)
-- ========================================================

local function normalizeUser(name)
  return trim(tostring(name or "")):lower():gsub("%s+", " ")
end

local function isDeveloper(name)
  return normalizeUser(name) == "ibrahim ansari"
end

local function isVerifiedUser(name)
  if isDeveloper(name) then return true end
  local n = normalizeUser(name)
  if n == "" then return false end
  for k, v in pairs(verified_users_map) do
    if normalizeUser(Uri.decode(tostring(k))) == n and (v == true or v == "true") then
      return true
    end
  end
  return false
end

local function isAdminUser(name)
  local n = normalizeUser(name)
  if n == "" then return false end
  for k, v in pairs(admin_users_map) do
    if normalizeUser(Uri.decode(tostring(k))) == n and (v == true or v == "true") then
      return true
    end
  end
  return false
end

local function isUserBlockedGlobal(name)
  local n = normalizeUser(name)
  if n == "" then return false end
  for k, v in pairs(blocked_users_map) do
    if normalizeUser(Uri.decode(tostring(k))) == n and (v == true or v == "true") then
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

local function getUserRoleStatusText(name)
  local roleTxt = isVerifiedUser(name) and "Verified" or (isAdminUser(name) and "Admin" or "Normal")
  local blkTxt = isUserBlockedGlobal(name) and "Blocked" or "Active"
  return roleTxt .. " • " .. blkTxt
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
  local my_norm = normalizeUser(current_username)
  for k, v in pairs(msg_tbl.played_by) do
    local un = type(v) == "string" and v or Uri.decode(tostring(k))
    if normalizeUser(un) == my_norm then
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
-- ONE-TIME INTRO & MESSAGE MILESTONE TRACKER (NO REPEAT AFTER SEEN)
-- ========================================================

local function getOneTimeRoomCuesMap()
  local raw = tostring(sp.getString("room_one_time_cues_json", "{}"))
  local ok, tbl = pcall(cjson.decode, raw)
  if ok and type(tbl) == "table" then return tbl end
  return {}
end

local function saveOneTimeRoomCuesMap(tbl)
  local ok, raw = pcall(cjson.encode, tbl)
  if ok and raw then
    sp.edit().putString("room_one_time_cues_json", raw).apply()
  end
end

local function collectRoomOneTimeNotices(msg_list)
  local notices = {}
  local seen_cues = getOneTimeRoomCuesMap()
  local changed = false

  local sender_first_msg = {}
  local sender_msg_count = {}

  for _, m in ipairs(msg_list) do
    local is_del = (m.deleted_for_everyone == true or m.deleted_for_everyone == "true")
    local s_raw = trim(tostring(m.sender or ""))
    if (not is_del) and s_raw ~= "" then
      local s_key = normalizeUser(s_raw)
      sender_msg_count[s_key] = (sender_msg_count[s_key] or 0) + 1
      if not sender_first_msg[s_key] then
        sender_first_msg[s_key] = {
          sender = s_raw,
          text = tostring(m.text or ""),
          is_voice = (m.msg_type == "voice")
        }
      end
    end
  end

  for s_key, info in pairs(sender_first_msg) do
    local intro_id = "intro_" .. encodeKey(s_key)
    if not seen_cues[intro_id] then
      seen_cues[intro_id] = true
      changed = true
      local snippet = info.is_voice and "Voice message" or trim(info.text)
      if #snippet > 80 then snippet = snippet:sub(1, 80) .. "..." end
      if snippet ~= "" then
        table.insert(notices, info.sender .. ": " .. snippet)
      end
    end

    local total_m = sender_msg_count[s_key] or 0
    local milestones = {100, 200, 500}
    for _, ms in ipairs(milestones) do
      if total_m >= ms then
        local ms_id = "mile_" .. encodeKey(s_key) .. "_" .. tostring(ms)
        if not seen_cues[ms_id] then
          seen_cues[ms_id] = true
          changed = true
          table.insert(notices, info.sender .. " reached " .. tostring(ms) .. " messages")
        end
      end
    end
  end

  local total_room_msgs = #msg_list
  local room_milestones = {100, 200, 500}
  for _, rms in ipairs(room_milestones) do
    if total_room_msgs >= rms then
      local r_id = "room_mile_" .. tostring(rms)
      if not seen_cues[r_id] then
        seen_cues[r_id] = true
        changed = true
        table.insert(notices, "BTP Voice Room reached " .. tostring(rms) .. " messages")
      end
    end
  end

  if changed then
    saveOneTimeRoomCuesMap(seen_cues)
  end

  return notices
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

local function stopActiveVoicePlayer(keep_queue)
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

  local is_me = (normalizeUser(msg_tbl.sender or "") == normalizeUser(current_username))
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

  local rx_tv = makeText("Reactions (" .. tostring(#detail_lines) .. "): " .. table.concat(summary_list, ", ") .. ". Tap to view.", 12)
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
    if callback then callback() end
    return
  end
  Http.get(FIREBASE_URL .. "verified_users.json", nil, "utf-8", nil, function(code, content)
    verified_users_map = {}
    if code == 200 and content and content ~= "null" then
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
    if callback then callback() end
    return
  end
  Http.get(FIREBASE_URL .. "admin_users.json", nil, "utf-8", nil, function(code, content)
    admin_users_map = {}
    if code == 200 and content and content ~= "null" then
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
    if callback then callback() end
    return
  end
  Http.get(FIREBASE_URL .. "settings/server_down.json", nil, "utf-8", nil, function(c1, r1)
    if c1 == 200 then
      server_is_down = (r1 == "true" or r1 == '"true"')
    end
    Http.get(FIREBASE_URL .. "settings/public_room_locked.json", nil, "utf-8", nil, function(c2, r2)
      if c2 == 200 then
        public_room_locked = (r2 == "true" or r2 == '"true"')
      end
      Http.get(FIREBASE_URL .. "settings/assistant_locked.json", nil, "utf-8", nil, function(c3, r3)
        if c3 == 200 then
          assistant_is_locked = (r3 == "true" or r3 == '"true"')
        end
        Http.get(FIREBASE_URL .. "settings/assistant_training.json", nil, "utf-8", nil, function(c4, r4)
          assistant_trained_items = {}
          if c4 == 200 and r4 and r4 ~= "null" then
            local ok_t, tdata = pcall(cjson.decode, r4)
            if ok_t and type(tdata) == "table" then
              for _, item in pairs(tdata) do
                if type(item) == "table" and trim(tostring(item.q or "")) ~= "" and trim(tostring(item.a or "")) ~= "" then
                  table.insert(assistant_trained_items, item)
                end
              end
            end
          end
          if callback then callback() end
        end)
      end)
    end)
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

local function getWhatsAppListTime(timestamp_raw, timestamp_str)
  local day_lbl = getDayLabelFromRaw(timestamp_raw)
  if day_lbl == "Today" then
    return tostring(timestamp_str or "Today")
  elseif day_lbl == "Yesterday" then
    return "Yesterday"
  elseif day_lbl ~= "" then
    return day_lbl
  end
  return tostring(timestamp_str or "")
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
    status = status_str or "online",
    last_seen = os.date("%I:%M %p, %d %b"),
    time_epoch = os.time()
  }
  http_post_or_put(FIREBASE_URL .. "user_presence/" .. encodeKey(current_username) .. ".json", "PUT", presence_data, function() end)
end

local function startPresenceTracking()
  updatePresence("online")
  if presence_handler == nil then
    presence_handler = Handler(Looper.getMainLooper())
    presence_runnable = Runnable({
      run = function()
        updatePresence("online")
        presence_handler.postDelayed(presence_runnable, 120000)
      end
    })
    presence_handler.postDelayed(presence_runnable, 120000)
  end
end

-- ========================================================
-- VOICE CHAT ROOM SESSION (START VOICE CHAT + NOTIFY + JOIN + ONLINE & MUTE STATUS)
-- ========================================================

function openActiveVoiceChatSessionDialog(session_id, initial_session_data)
  if active_voice_chat_dialog ~= nil then return end
  active_voice_chat_id = session_id

  local is_muted_local = false
  local is_speaking_local = false
  local session_active = true
  local seen_pkt_ids = {}
  local session_open_ts = os.date("%Y%m%d%H%M%S")
  local rec_obj = nil
  local rec_sec = 0
  local rec_path = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_vc_burst.m4a"

  http_post_or_put(FIREBASE_URL .. "room_voice_chats/" .. session_id .. "/participants/" .. encodeKey(current_username) .. ".json", "PUT", current_username, function() end)
  http_post_or_put(FIREBASE_URL .. "room_voice_chats/" .. session_id .. "/muted/" .. encodeKey(current_username) .. ".json", "PUT", false, function() end)

  local layout = makeLayout(true, 16)
  local room_label = tostring(initial_session_data.room_name or "BTP Voice Room")

  local status_tv = makeText("Voice chat active in " .. room_label, 15)
  status_tv.setTextColor(0xFF0D47A1)
  layout.addView(status_tv)

  local participants_tv = makeText("Participants: Loading...", 13)
  participants_tv.setPadding(0, 8, 0, 12)
  layout.addView(participants_tv)

  local ctrl_row = makeLayout(false, 4)
  local mute_btn = makeButton("Mute")
  mute_btn.setContentDescription("Mute")
  local speak_btn = makeButton("Hold or Tap to Speak")
  speak_btn.setContentDescription("Speak in voice chat")
  ctrl_row.addView(mute_btn, LinearLayout.LayoutParams(0, -2, 1))
  ctrl_row.addView(speak_btn, LinearLayout.LayoutParams(0, -2, 1))
  layout.addView(ctrl_row)

  local leave_btn = makeButton("Leave Voice Chat")
  leave_btn.setBackgroundColor(0xFFD32F2F)
  leave_btn.setTextColor(0xFFFFFFFF)
  layout.addView(leave_btn, LinearLayout.LayoutParams(-1, -2))

  local dlg = AlertDialog.Builder(activity)
    .setTitle("Voice Chat - " .. room_label)
    .setView(layout)
    .setCancelable(false)
    .create()
  active_voice_chat_dialog = dlg
  dlg.show()

  local poll_h = Handler(Looper.getMainLooper())
  local poll_r = nil
  local rec_h = Handler(Looper.getMainLooper())
  local rec_r = nil

  local function stopRecBurst(send_it)
    is_speaking_local = false
    speak_btn.setText("Tap to Speak")
    if rec_r then
      pcall(function() rec_h.removeCallbacks(rec_r) end)
      rec_r = nil
    end
    if rec_obj then
      pcall(function()
        rec_obj.stop()
        rec_obj.release()
      end)
      rec_obj = nil
    end
    if send_it then
      local b64 = encodeFileToBase64(rec_path)
      if b64 and b64 ~= "" then
        local pkt = {
          sender = current_username,
          duration = rec_sec > 0 and rec_sec or 1,
          audio_base64 = b64,
          timestamp_raw = os.date("%Y%m%d%H%M%S")
        }
        http_post_or_put(FIREBASE_URL .. "room_voice_chats/" .. session_id .. "/packets.json", "POST", pkt, function() end)
      end
    end
    rec_sec = 0
  end

  local function cleanupVoiceChat()
    session_active = false
    stopRecBurst(false)
    active_voice_chat_dialog = nil
    active_voice_chat_id = nil
    if poll_r then
      pcall(function() poll_h.removeCallbacks(poll_r) end)
      poll_r = nil
    end
    pcall(function()
      local am = activity.getSystemService(Context.AUDIO_SERVICE)
      am.setMicrophoneMute(false)
      am.setMode(AudioManager.MODE_NORMAL)
    end)
  end

  leave_btn.setOnClickListener(function()
    http_delete(FIREBASE_URL .. "room_voice_chats/" .. session_id .. "/participants/" .. encodeKey(current_username) .. ".json", function() end)
    http_delete(FIREBASE_URL .. "room_voice_chats/" .. session_id .. "/muted/" .. encodeKey(current_username) .. ".json", function() end)
    cleanupVoiceChat()
    pcall(function() dlg.dismiss() end)
    showToast("Left voice chat.")
  end)

  mute_btn.setOnClickListener(function()
    is_muted_local = not is_muted_local
    pcall(function()
      local am = activity.getSystemService(Context.AUDIO_SERVICE)
      am.setMode(AudioManager.MODE_IN_COMMUNICATION)
      am.setMicrophoneMute(is_muted_local)
    end)
    local lbl = is_muted_local and "Unmute" or "Mute"
    mute_btn.setText(lbl)
    mute_btn.setContentDescription(lbl)
    http_post_or_put(FIREBASE_URL .. "room_voice_chats/" .. session_id .. "/muted/" .. encodeKey(current_username) .. ".json", "PUT", is_muted_local, function() end)
    showToast(is_muted_local and "You are muted." or "You are unmuted.")
  end)

  speak_btn.setOnClickListener(function()
    if is_muted_local then
      showToast("Unmute first to speak.")
      return
    end
    if not is_speaking_local then
      local f = File(rec_path)
      if f.exists() then f.delete() end
      rec_obj = startHighClarityRecording(rec_path)
      if not rec_obj then
        showToast("Microphone unavailable.")
        return
      end
      is_speaking_local = true
      rec_sec = 0
      speak_btn.setText("Send Voice (0s)")
      rec_r = Runnable({
        run = function()
          if is_speaking_local and session_active then
            rec_sec = rec_sec + 1
            speak_btn.setText("Send Voice (" .. tostring(rec_sec) .. "s)")
            if rec_sec >= 15 then
              stopRecBurst(true)
            else
              rec_h.postDelayed(rec_r, 1000)
            end
          end
        end
      })
      rec_h.postDelayed(rec_r, 1000)
    else
      stopRecBurst(true)
    end
  end)

  local function refreshVoiceChatRoom()
    if not session_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "room_voice_chats/" .. session_id .. ".json", function(s, r)
      if not session_active then return end
      if not s or not r or r == "null" then
        cleanupVoiceChat()
        pcall(function() dlg.dismiss() end)
        return
      end
      local ok, sdata = pcall(cjson.decode, r)
      if not ok or type(sdata) ~= "table" then return end

      if tostring(sdata.status or "active") == "ended" then
        cleanupVoiceChat()
        pcall(function() dlg.dismiss() end)
        showToast("Voice chat ended.")
        return
      end

      http_get(FIREBASE_URL .. "user_presence.json", function(sp_ok, sp_raw)
        if not session_active then return end
        local pdata = {}
        if sp_ok and sp_raw and sp_raw ~= "null" then
          local ok_p, dec_p = pcall(cjson.decode, sp_raw)
          if ok_p and type(dec_p) == "table" then pdata = dec_p end
        end
        local now = os.time()
        local muted_map = type(sdata.muted) == "table" and sdata.muted or {}
        local lines = {}

        if type(sdata.participants) == "table" then
          for pk, pv in pairs(sdata.participants) do
            local pname = type(pv) == "string" and pv or Uri.decode(tostring(pk))
            if trim(pname) ~= "" then
              local p_entry = pdata[encodeKey(pname)] or pdata[pname]
              local is_on = (normalizeUser(pname) == normalizeUser(current_username)) or
                (type(p_entry) == "table" and p_entry.status == "online" and (now - tonumber(p_entry.time_epoch or 0) < 180))
              local state_str = is_on and "Online" or "Offline"
              local is_m = (muted_map[encodeKey(pname)] == true or muted_map[pname] == true)
              if is_m then
                state_str = state_str .. ", Muted"
              end
              table.insert(lines, getVerifiedName(pname) .. " - " .. state_str)
            end
          end
        end

        if #lines == 0 then
          table.insert(lines, getVerifiedName(current_username) .. " - Online")
        end
        participants_tv.setText("Participants:\n" .. table.concat(lines, "\n"))
      end)

      if type(sdata.packets) == "table" then
        local pkts = {}
        for pid, pkt in pairs(sdata.packets) do
          if type(pkt) == "table" then
            pkt.id = pid
            table.insert(pkts, pkt)
          end
        end
        table.sort(pkts, function(a, b)
          return tostring(a.timestamp_raw or "") < tostring(b.timestamp_raw or "")
        end)
        for _, pkt in ipairs(pkts) do
          if not seen_pkt_ids[pkt.id] then
            seen_pkt_ids[pkt.id] = true
            if normalizeUser(pkt.sender or "") ~= normalizeUser(current_username) and tostring(pkt.timestamp_raw or "") >= session_open_ts then
              local out_p = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_vcpkt_" .. tostring(pkt.id):gsub("[^%w_]", "_") .. ".m4a"
              if decodeBase64ToFile(pkt.audio_base64, out_p) then
                pcall(function()
                  local mp = MediaPlayer()
                  mp.setDataSource(out_p)
                  mp.prepare()
                  mp.start()
                  mp.setOnCompletionListener(MediaPlayer.OnCompletionListener{
                    onCompletion = function(m) pcall(function() m.release() end) end
                  })
                end)
              end
            end
          end
        end
      end
    end)
  end

  refreshVoiceChatRoom()
  poll_r = Runnable({
    run = function()
      if session_active then
        refreshVoiceChatRoom()
        poll_h.postDelayed(poll_r, 2500)
      end
    end
  })
  poll_h.postDelayed(poll_r, 2500)
end

local function startRoomVoiceChatSession(room_label)
  if notifyServerDownIfNeeded() then return end
  local sid = "vc_" .. tostring(os.time()) .. "_" .. tostring(math.random(100, 999))
  local parts = {}
  parts[encodeKey(current_username)] = current_username
  local payload = {
    id = sid,
    room_name = room_label or "BTP Voice Room",
    host = current_username,
    status = "active",
    created_epoch = os.time(),
    participants = parts,
    muted = {}
  }
  http_post_or_put(FIREBASE_URL .. "room_voice_chats/" .. sid .. ".json", "PUT", payload, function(ok)
    if ok then
      playSound(SOUND_CALL_CONNECTED, nil, ToneGenerator.TONE_PROP_ACK, false)
      openActiveVoiceChatSessionDialog(sid, payload)
    else
      showToast("Unable to start voice chat.")
    end
  end)
end

-- ========================================================
-- VOICE CALL ENGINE (0-15s LOOP VOICEMAIL, CLEAN STOP, TIMEOUT, ACCESSIBLE LABELS)
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
        if data.status == "online" and (now - last_t < 180) then
          if callback then callback(true) end
          return
        end
      end
    end
    if callback then callback(false) end
  end)
end

local function sendVoicePacketInCall(call_id, duration_sec, file_path)
  local b64 = encodeFileToBase64(file_path)
  if not b64 or b64 == "" then return end
  local pkt = {
    sender = current_username,
    duration = duration_sec,
    audio_base64 = b64,
    timestamp_raw = os.date("%Y%m%d%H%M%S")
  }
  http_post_or_put(FIREBASE_URL .. "voice_calls/" .. call_id .. "/packets.json", "POST", pkt, function() end)
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

  local status_tv = makeText("Connecting voice call with " .. call_label, 15)
  status_tv.setTextColor(0xFF0D47A1)
  layout.addView(status_tv)

  local participants_tv = makeText("Participants: Loading...", 13)
  participants_tv.setPadding(0, 6, 0, 10)
  layout.addView(participants_tv)

  local ctrl_row_1 = makeLayout(false, 4)
  local mute_btn = makeButton("Mute Microphone")
  mute_btn.setContentDescription("Mute Microphone")
  local speaker_btn = makeButton("Speaker Off")
  speaker_btn.setContentDescription("Speaker Off")
  ctrl_row_1.addView(mute_btn, LinearLayout.LayoutParams(0, -2, 1))
  ctrl_row_1.addView(speaker_btn, LinearLayout.LayoutParams(0, -2, 1))
  layout.addView(ctrl_row_1)

  local ctrl_row_2 = makeLayout(false, 4)
  local add_person_btn = makeButton("Add Person to Call")
  local push_voice_btn = makeButton("Tap to Speak Voice")
  ctrl_row_2.addView(add_person_btn, LinearLayout.LayoutParams(0, -2, 1))
  ctrl_row_2.addView(push_voice_btn, LinearLayout.LayoutParams(0, -2, 1))
  layout.addView(ctrl_row_2)

  local end_call_btn = makeButton("End Call")
  end_call_btn.setBackgroundColor(0xFFD32F2F)
  end_call_btn.setTextColor(0xFFFFFFFF)
  layout.addView(end_call_btn, LinearLayout.LayoutParams(-1, -2))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Voice Call - " .. call_label)
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
  local seen_pkt_ids = {}
  local call_start_ts = os.date("%Y%m%d%H%M%S")
  local is_recording_burst = false
  local burst_recorder = nil
  local burst_sec = 0
  local burst_timer_h = Handler(Looper.getMainLooper())
  local burst_timer_r = nil
  local burst_path = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_call_burst.m4a"

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
    if burst_timer_r then
      pcall(function() burst_timer_h.removeCallbacks(burst_timer_r) end)
      burst_timer_r = nil
    end
    if burst_recorder then
      pcall(function()
        burst_recorder.stop()
        burst_recorder.release()
      end)
      burst_recorder = nil
    end
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
    showToast(active_call_speaker_on and "Earpiece mode." or "Speaker on.")
  end)

  local function finishSpeakBurst()
    is_recording_burst = false
    push_voice_btn.setText("Tap to Speak Voice")
    if burst_timer_r then
      pcall(function() burst_timer_h.removeCallbacks(burst_timer_r) end)
      burst_timer_r = nil
    end
    local sec = burst_sec > 0 and burst_sec or 1
    burst_sec = 0
    if burst_recorder then
      pcall(function()
        burst_recorder.stop()
        burst_recorder.release()
      end)
      burst_recorder = nil
    end
    sendVoicePacketInCall(call_id, sec, burst_path)
  end

  push_voice_btn.setOnClickListener(function()
    if active_call_is_muted then
      showToast("Unmute microphone first to speak.")
      return
    end
    if not is_recording_burst then
      local f = File(burst_path)
      if f.exists() then f.delete() end
      burst_recorder = startHighClarityRecording(burst_path)
      if not burst_recorder then
        showToast("Microphone unavailable.")
        return
      end
      is_recording_burst = true
      burst_sec = 0
      push_voice_btn.setText("Send Voice Now (0s)")
      burst_timer_r = Runnable({
        run = function()
          if is_recording_burst and call_active then
            burst_sec = burst_sec + 1
            push_voice_btn.setText("Send Voice Now (" .. tostring(burst_sec) .. "s)")
            if burst_sec >= 15 then
              finishSpeakBurst()
            else
              burst_timer_h.postDelayed(burst_timer_r, 1000)
            end
          end
        end
      })
      burst_timer_h.postDelayed(burst_timer_r, 1000)
    else
      finishSpeakBurst()
    end
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
              if uname and uname ~= "" and normalizeUser(uname) ~= normalizeUser(current_username) then
                local pe = pdata[encodeKey(uname)] or pdata[uname]
                if type(pe) == "table" and pe.status == "online" and (now - tonumber(pe.time_epoch or 0) < 180) then
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
                  showToast("Added " .. invite_user .. " to call.")
                end)
              end)
            end
          }).show()
      end)
    end)
  end)

  local function refreshCallStateAndAudio()
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
          local tag = getVerifiedName(pname) .. " - Online"
          if is_m then tag = tag .. ", Muted" end
          table.insert(part_names, tag)
        end
      end
      if #part_names == 0 then
        table.insert(part_names, getVerifiedName(current_username) .. " - Online")
      end
      participants_tv.setText("In Call: " .. table.concat(part_names, ", "))

      if c_status == "active" then
        triggerConnectedSoundOnce()
        status_tv.setText("Connected - " .. call_label)
      else
        status_tv.setText("Ringing " .. call_label)
      end

      if type(cdata.packets) == "table" then
        local sorted_pkts = {}
        for pid, pkt in pairs(cdata.packets) do
          if type(pkt) == "table" then
            pkt.id = pid
            table.insert(sorted_pkts, pkt)
          end
        end
        table.sort(sorted_pkts, function(a, b)
          return tostring(a.timestamp_raw or "") < tostring(b.timestamp_raw or "")
        end)
        for _, pkt in ipairs(sorted_pkts) do
          if not seen_pkt_ids[pkt.id] then
            seen_pkt_ids[pkt.id] = true
            if normalizeUser(pkt.sender or "") ~= normalizeUser(current_username) and tostring(pkt.timestamp_raw or "") >= call_start_ts then
              local out_p = tostring(activity.getCacheDir().getAbsolutePath()) .. "/btp_cpkt_" .. tostring(pkt.id):gsub("[^%w_]", "_") .. ".m4a"
              if decodeBase64ToFile(pkt.audio_base64, out_p) then
                pcall(function()
                  local mp = MediaPlayer()
                  mp.setDataSource(out_p)
                  mp.prepare()
                  mp.start()
                  mp.setOnCompletionListener(MediaPlayer.OnCompletionListener{
                    onCompletion = function(m) pcall(function() m.release() end) end
                  })
                end)
              end
            end
          end
        end
      end
    end)
  end

  refreshCallStateAndAudio()

  poll_runnable = Runnable({
    run = function()
      if call_active then
        refreshCallStateAndAudio()
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
        if normalizeUser(mname) ~= normalizeUser(current_username) then
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
      status = "ringing",
      created_epoch = os.time(),
      participants = parts,
      invited = invited
    }

    http_post_or_put(FIREBASE_URL .. "voice_calls/" .. call_id .. ".json", "PUT", call_payload, function(ok)
      if ok then
        openActiveCallSessionDialog(call_id, call_payload, true)
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

local seen_voice_chat_invites = {}

local function startIncomingCallWatcher()
  if incoming_call_handler ~= nil then return end
  incoming_call_handler = Handler(Looper.getMainLooper())
  incoming_call_runnable = Runnable({
    run = function()
      if current_username ~= "" and isNetworkAvailable() then
        local my_norm = normalizeUser(current_username)
        local now = os.time()

        if active_call_dialog == nil then
          http_get(FIREBASE_URL .. "voice_calls.json", function(s, r)
            if s and r and r ~= "null" and active_call_dialog == nil then
              local ok, calls = pcall(cjson.decode, r)
              if ok and type(calls) == "table" then
                for cid, cdata in pairs(calls) do
                  if type(cdata) == "table" and tostring(cdata.status or "") == "ringing" and (now - tonumber(cdata.created_epoch or 0) < CALL_RING_TIMEOUT_SEC) then
                    local is_invited = false
                    if type(cdata.invited) == "table" then
                      for ik, iv in pairs(cdata.invited) do
                        local iname = type(iv) == "string" and iv or Uri.decode(tostring(ik))
                        if normalizeUser(iname) == my_norm then
                          is_invited = true
                          break
                        end
                      end
                    end
                    if is_invited and normalizeUser(cdata.caller or "") ~= my_norm then
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
                        and ("Incoming Group Call from " .. getVerifiedName(caller_name) .. " in " .. ctitle)
                        or ("Incoming Voice Call from " .. getVerifiedName(caller_name))

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
                      break
                    end
                  end
                end
              end
            end
          end)
        end

        if active_voice_chat_dialog == nil then
          http_get(FIREBASE_URL .. "room_voice_chats.json", function(sv, rv)
            if sv and rv and rv ~= "null" and active_voice_chat_dialog == nil then
              local okv, vchats = pcall(cjson.decode, rv)
              if okv and type(vchats) == "table" then
                for sid, sdata in pairs(vchats) do
                  if type(sdata) == "table" and tostring(sdata.status or "active") == "active" and (now - tonumber(sdata.created_epoch or 0) < 3600) then
                    if normalizeUser(sdata.host or "") ~= my_norm and not seen_voice_chat_invites[sid] then
                      seen_voice_chat_invites[sid] = true
                      playSound(SOUND_ALERT_ANNOUNCE, nil, ToneGenerator.TONE_PROP_BEEP2, false)
                      AlertDialog.Builder(activity)
                        .setTitle("Voice Chat Started")
                        .setMessage(getVerifiedName(sdata.host or "Member") .. " started a voice chat in " .. tostring(sdata.room_name or "BTP Voice Room") .. ". Would you like to join?")
                        .setPositiveButton("Join Voice Chat", DialogInterface.OnClickListener{
                          onClick = function()
                            openActiveVoiceChatSessionDialog(sid, sdata)
                          end
                        })
                        .setNegativeButton("Ignore", nil)
                        .show()
                      break
                    end
                  end
                end
              end
            end
          end)
        end
      end
      if incoming_call_handler and incoming_call_runnable then
        incoming_call_handler.postDelayed(incoming_call_runnable, 3500)
      end
    end
  })
  incoming_call_handler.postDelayed(incoming_call_runnable, 3500)
end

-- ========================================================
-- BTP ASSISTANT ENGINE (RESILIENT API + TRAINING Q&A + FEEDBACK + LOCK)
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

local function buildAppCodesContextSummary()
  if type(all_codes_data) ~= "table" or #all_codes_data == 0 then
    return "Shared Lua codes feed is available inside Home tab."
  end
  local lines = {}
  local maxItems = math.min(6, #all_codes_data)
  for i = 1, maxItems do
    local c = all_codes_data[i]
    table.insert(lines, tostring(c.title or "Untitled") .. " by " .. tostring(c.author or "Anonymous"))
  end
  return table.concat(lines, "; ")
end

local function buildTrainedKnowledgeContext()
  if type(assistant_trained_items) ~= "table" or #assistant_trained_items == 0 then
    return ""
  end
  local out = {}
  for i = 1, math.min(12, #assistant_trained_items) do
    local it = assistant_trained_items[i]
    table.insert(out, "Q: " .. tostring(it.q or "") .. " -> A: " .. tostring(it.a or ""))
  end
  return table.concat(out, "\n")
end

local function findLocalTrainedAnswer(queryStr)
  local qLow = trim(tostring(queryStr or "")):lower()
  if qLow == "" then return nil end
  for _, item in ipairs(assistant_trained_items) do
    local kLow = trim(tostring(item.q or "")):lower()
    if kLow ~= "" and (qLow:find(kLow, 1, true) or kLow:find(qLow, 1, true)) then
      return tostring(item.a or "")
    end
  end
  return nil
end

local function isFeedbackRequestText(queryStr)
  local l = trim(tostring(queryStr or "")):lower()
  return (l:find("feedback", 1, true) ~= nil or l:find("sugjav", 1, true) ~= nil or l:find("sujhav", 1, true) ~= nil or l:find("report", 1, true) ~= nil)
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

local function fetchAssistantReplyWithFallback(modelObj, promptText, fallbackQuery, callback)
  local matchedLocal = findLocalTrainedAnswer(fallbackQuery)
  if matchedLocal and matchedLocal ~= "" then
    callback(true, matchedLocal)
    return
  end

  local mId = (modelObj and modelObj.backendId) or "gpt-sol"
  local primaryUrl = "https://ai-hub.schoolofmindlight.workers.dev/?model=" .. URLEncoder.encode(mId, "UTF-8") .. "&chat=" .. URLEncoder.encode(promptText, "UTF-8")

  Http.get(primaryUrl, nil, "UTF-8", nil, function(code1, content1)
    if code1 == 200 and content1 and trim(tostring(content1)) ~= "" then
      local reply1 = content1
      local ok1, parsed1 = pcall(cjson.decode, content1)
      if ok1 and type(parsed1) == "table" then
        reply1 = parsed1.reply or parsed1.response or parsed1.message or parsed1.text or content1
      end
      reply1 = trim(tostring(reply1))
      if reply1 ~= "" and not reply1:lower():find("error", 1, true) then
        callback(true, reply1)
        return
      end
    end

    local secUrl = "https://text.pollinations.ai/" .. URLEncoder.encode(promptText:sub(1, 550), "UTF-8") .. "?model=openai"
    Http.get(secUrl, nil, "UTF-8", nil, function(code2, content2)
      if code2 == 200 and content2 and trim(tostring(content2)) ~= "" then
        callback(true, trim(tostring(content2)))
      else
        callback(false, "")
      end
    end)
  end)
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
    local clean = stripAssistantMarkdownEmojis(txt)
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
          local trainedCtx = buildTrainedKnowledgeContext()
          local prompt = "You are BTP Assistant inside " .. APP_TITLE .. " by Ibrahim Ansari. User: " .. uname .. ". Codes: " .. buildAppCodesContextSummary() .. (trainedCtx ~= "" and ("\nLearned:\n" .. trainedCtx) or "") .. "\nUser: " .. spoken .. "\nReply briefly without emojis."
          fetchAssistantReplyWithFallback({backendId = "gpt-sol"}, prompt, spoken, function(ok, reply)
            if not isLive then return end
            if ok and reply ~= "" then
              speakLiveReply(reply)
            else
              speakLiveReply("Abhi reply generate karne mein thodi der ho rahi hai, kripya dobara boliye.")
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
        speakLiveReply("Hello " .. uname .. ", main BTP Assistant hoon. App ya codes ke baare mein kuchh bhi poochhiye.")
      end
    end
  }, 800)
end

function openBTPAssistantDialog()
  if notifyServerDownIfNeeded() then return end

  local uname = (current_username ~= "" and current_username) or "User"
  local ast_models = {
    {displayName = "BTP 1.4 (Default)", backendId = "gpt-sol"},
    {displayName = "Blind Tech Power Pro", backendId = "gpt-5.5"},
    {displayName = "BTP Ultra 2.0", backendId = "claude-sonnet"},
    {displayName = "BTP Vision & Smart", backendId = "gemini-pro"},
    {displayName = "BTP Flash (Fast)", backendId = "gemini-flash"}
  }
  local model_idx = sp.getInt("btp_ast_model_idx", 1)
  local mem_enabled = sp.getBoolean("btp_ast_mem_on", true)
  local auto_tts = sp.getBoolean("btp_ast_auto_tts", false)
  local saved_mem = tostring(sp.getString("btp_ast_memory", ""))
  local chatHistory = {}
  if mem_enabled and saved_mem ~= "" then
    table.insert(chatHistory, saved_mem:sub(-500))
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

    local bodyTv = makeText(sender .. ":\n" .. tostring(textStr or ""), 14)
    bodyTv.setTextIsSelectable(true)
    bubble.addView(bodyTv)

    if isReply then
      local row = makeLayout(false, 4)
      local listenBtn = makeButton("Preparing Voice...")
      listenBtn.setEnabled(false)
      row.addView(listenBtn)

      local codeSnippet = extractLuaCode(tostring(textStr or ""))
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
      generateAssistantSpeechFile(tostring(textStr or ""), "hi", mp3Path, function(ok, savedP)
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
            generateAssistantSpeechFile(tostring(textStr or ""), "hi", mp3Path, function(ok2, p2)
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
    if assistant_is_locked then
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

  appendAstBubble("BTP Assistant", "Hello " .. uname .. "! Main BTP Assistant hoon. App ke features, shared Lua codes, feedback, ya kisi bhi sawal ke liye poochhiye.", true, false)

  local function runAssistantQuery(userQuery)
    if notifyServerDownIfNeeded() then return end
    if assistant_is_locked then
      refreshAssistantLockView()
      showToast("Assistant is currently locked.")
      return
    end

    local q = trim(userQuery)
    if q == "" then return end

    if isGenerating then
      isGenerating = false
      reqSeq = reqSeq + 1
      statusTv.setVisibility(View.GONE)
      sendBtn.setText("Send")
      return
    end

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
    local trainedCtx = buildTrainedKnowledgeContext()
    local sysPrompt = "You are BTP Assistant (" .. chosenModel.displayName .. ") inside '" .. APP_TITLE .. "' by Ibrahim Ansari. Codes: " .. buildAppCodesContextSummary() .. ". "
      .. (trainedCtx ~= "" and ("Learned Q&A:\n" .. trainedCtx .. "\n") or "")
      .. (mem_enabled and #chatHistory > 0 and ("Context:\n" .. table.concat(chatHistory, "\n") .. "\n") or "")
      .. "User (" .. uname .. "): " .. q .. "\nReply clearly and concisely without emojis."
    if #sysPrompt > 1100 then sysPrompt = sysPrompt:sub(-1100) end

    fetchAssistantReplyWithFallback(chosenModel, sysPrompt, q, function(ok, reply)
      if (not isGenerating) or (curReq ~= reqSeq) then return end
      isGenerating = false
      statusTv.setVisibility(View.GONE)
      sendBtn.setText("Send")

      if ok and reply ~= "" then
        local cleanReply = trim(tostring(reply))
        appendAstBubble("BTP Assistant", cleanReply, true, true)
        if mem_enabled then
          table.insert(chatHistory, uname .. ": " .. q:sub(1, 100))
          table.insert(chatHistory, "Assistant: " .. cleanReply:sub(1, 140))
          if #chatHistory > 4 then
            table.remove(chatHistory, 1)
            table.remove(chatHistory, 1)
          end
          sp.edit().putString("btp_ast_memory", table.concat(chatHistory, "\n")).apply()
        end
      else
        appendAstBubble("BTP Assistant", "Abhi response server se jawab nahi mil paaya. Kripya thodi der baad dubara try karein.", true, false)
      end
    end)
  end

  sendBtn.setOnClickListener(function()
    runAssistantQuery(tostring(msgInput.getText()))
  end)

  micBtn.setOnClickListener(function()
    if assistant_is_locked then
      refreshAssistantLockView()
      showToast("Assistant is currently locked.")
      return
    end
    if isMicBusy then return end
    isMicBusy = true
    stopAstAudio()
    pcall(function()
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
          pcall(function() micRec.cancel() micRec.destroy() micRec = nil end)
        end,
        onResults = function(res)
          if done then return end
          done = true
          isMicBusy = false
          micBtn.setText("Microphone")
          local matches = res.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
          pcall(function() micRec.cancel() micRec.destroy() micRec = nil end)
          if matches and matches.size() > 0 then
            runAssistantQuery(tostring(matches.get(0)))
          end
        end,
        onPartialResults = function() end,
        onEvent = function() end
      })
      micRec.startListening(it)
    end)
  end)

  moreBtn.setOnClickListener(function()
    local curM = ast_models[model_idx] or ast_models[1]
    local opts = {
      "Open BTP Live Voice Mode",
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
          elseif w == 2 then
            auto_tts = not auto_tts
            sp.edit().putBoolean("btp_ast_auto_tts", auto_tts).apply()
            showToast("Auto TTS: " .. (auto_tts and "ON" or "OFF"))
          elseif w == 3 then
            mem_enabled = not mem_enabled
            sp.edit().putBoolean("btp_ast_mem_on", mem_enabled).apply()
            showToast("Memory: " .. (mem_enabled and "ON" or "OFF"))
          elseif w == 4 then
            awaitingFeedbackInput = true
            appendAstBubble("BTP Assistant", "Apna feedback type karein aur Send dabayein.", true, false)
          elseif w == 5 then
            chatHistory = {}
            sp.edit().putString("btp_ast_memory", "").apply()
            showToast("Assistant memory cleared.")
          elseif w == 6 then
            showMessage("About BTP Assistant", "Name: BTP Assistant\nPlatform: " .. APP_TITLE .. "\nDeveloper: " .. APP_DEV .. "\nVersion: " .. APP_VERSION .. "\nModel: " .. curM.displayName)
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
-- ASSISTANT MANAGEMENT DIALOG (LOCK + TRAIN Q&A + VIEW FEEDBACKS)
-- ========================================================

local function showAssistantManagementDialog()
  if not isVerifiedUser(current_username) then
    showToast("Only verified users can access Assistant Management.")
    return
  end

  local layout = makeLayout(true, 14)
  local lockBtn = makeButton(assistant_is_locked and "Unlock BTP Assistant (Currently Locked)" or "Lock BTP Assistant (Hide Input for Users)")
  local trainBtn = makeButton("Train Assistant (Add / View Q&A Knowledge)")
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
      .setTitle("Train BTP Assistant")
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
            if ok then showToast("Assistant trained with new knowledge.") end
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
-- SILENT AUTO-CLEANUP (CHATS 7D + INACTIVE GROUPS <5 MEMBERS IN 3D)
-- ========================================================

local function runSilentAutoCleanup()
  if not isNetworkAvailable() then return end
  pcall(function()
    local now = os.time()
    local seven_days_sec = 7 * 86400
    local three_days_sec = 3 * 86400
    local cutoff_epoch = now - seven_days_sec
    local cutoff_raw = os.date("%Y%m%d%H%M%S", cutoff_epoch)

    http_get(FIREBASE_URL .. "personal_chats.json", function(s, r)
      if s and r and r ~= "null" then
        local ok, data = pcall(cjson.decode, r)
        if ok and type(data) == "table" then
          for room_key, msgs in pairs(data) do
            if type(msgs) == "table" then
              local all_expired = true
              for mid, m in pairs(msgs) do
                if type(m) == "table" then
                  local m_raw = tostring(m.timestamp_raw or "")
                  if m_raw ~= "" and m_raw < cutoff_raw then
                    http_delete(FIREBASE_URL .. "personal_chats/" .. room_key .. "/" .. mid .. ".json", function() end)
                  else
                    all_expired = false
                  end
                end
              end
              if all_expired then
                http_delete(FIREBASE_URL .. "personal_chats/" .. room_key .. ".json", function() end)
              end
            end
          end
        end
      end
    end)

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

    http_get(FIREBASE_URL .. "codes.json", function(s, r)
      if s and r and r ~= "null" then
        local ok, data = pcall(cjson.decode, r)
        if ok and type(data) == "table" then
          local code_list = {}
          for k, v in pairs(data) do
            if type(v) == "table" then
              table.insert(code_list, { id = k, ts = tostring(v.timestamp_raw or v.timestamp or "") })
            end
          end
          if #code_list > 100 then
            table.sort(code_list, function(a, b) return a.ts < b.ts end)
            local excess = #code_list - 100
            for i = 1, excess do
              http_delete(FIREBASE_URL .. "codes/" .. code_list[i].id .. ".json", function() end)
            end
          end
        end
      end
    end)
  end)
end

-- ========================================================
-- ONE-TIME POPUP ANNOUNCEMENT NOTE CHECKER
-- ========================================================

local function checkPopupAnnouncementNote()
  if not isNetworkAvailable() then return end
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
            end
          })
          .show()
      end
    end
  end)
end

-- ========================================================
-- CHECK GLOBAL ADMIN BLOCK STATUS
-- ========================================================

local function checkBlockStatus(onNotBlocked)
  if current_username == "" or isDeveloper(current_username) then
    if onNotBlocked then onNotBlocked() end
    return
  end

  http_get(FIREBASE_URL .. "blocked/" .. encodeKey(current_username) .. ".json", function(success, response)
    if success and response and (response == "true" or response == '"true"') then
      local layout = makeLayout(true, 20)
      layout.addView(makeText("Access Denied.\nYou have been blocked by the admin due to policy violations.", 15))
      
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
    "WELCOME TO\n" .. APP_TITLE .. "\n\n"
    .. APP_DEV .. "\nVersion: " .. APP_VERSION .. "\n\n"
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
        showToast("Please enter your name to proceed.")
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
      checkForAppUpdate(false)
    end
  })
end

local function copyCode(code)
  local clipboard = activity.getSystemService(Context.CLIPBOARD_SERVICE)
  clipboard.setText(tostring(code or ""))
  showToast("Code copied to clipboard.")
end

-- ========================================================
-- NOTIFICATIONS & LIKE SOUND WATCHER
-- ========================================================

local function stopBackgroundNotificationWatcher()
  if bg_notif_handler ~= nil and bg_notif_runnable ~= nil then
    pcall(function()
      bg_notif_handler.removeCallbacks(bg_notif_runnable)
    end)
    bg_notif_handler = nil
    bg_notif_runnable = nil
  end
end

function updateNotificationCount(silent)
  if not notif_button or not isNetworkAvailable() then return end
  
  local seen_map = getSeenNotifsMap()

  http_get(FIREBASE_URL .. "codes.json", function(success, response)
    if not success or not response or response == "null" then return end

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

          if normalizeUser(v.author or "") == normalizeUser(current_username) then
            if v.likes then
              for liker, _ in pairs(v.likes) do
                local dec_liker = Uri.decode(tostring(liker))
                if normalizeUser(dec_liker) ~= normalizeUser(current_username) then
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
                if c.user and normalizeUser(c.user) ~= normalizeUser(current_username) then
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
  if not sp.getBoolean("notif_sound_enabled", false) then return end
  if bg_notif_handler == nil then
    bg_notif_handler = Handler(Looper.getMainLooper())
    bg_notif_runnable = Runnable({
      run = function()
        if isNetworkAvailable() and sp.getBoolean("notif_sound_enabled", false) then
          updateNotificationCount(false)
          if bg_notif_handler and bg_notif_runnable then
            bg_notif_handler.postDelayed(bg_notif_runnable, 30000)
          end
        else
          stopBackgroundNotificationWatcher()
        end
      end
    })
    bg_notif_handler.postDelayed(bg_notif_runnable, 30000)
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
            if type(v) == "table" and normalizeUser(v.author or "") == normalizeUser(current_username) then
              if v.likes then
                for liker, _ in pairs(v.likes) do
                  local decoded_liker = Uri.decode(tostring(liker))
                  if normalizeUser(decoded_liker) ~= normalizeUser(current_username) then
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
                  if c.user and normalizeUser(c.user) ~= normalizeUser(current_username) then
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
-- PERSONAL CHAT (1-ON-1 WITH VOICE CALL + SEEN BY + DELETE LOCK)
-- ========================================================

local function getSymmetricChatKey(u1, u2)
  local s1 = normalizeUser(u1)
  local s2 = normalizeUser(u2)
  if s1 < s2 then
    return encodeKey(s1) .. "_" .. encodeKey(s2)
  else
    return encodeKey(s2) .. "_" .. encodeKey(s1)
  end
end

function openPersonalChat(target_user)
  local layout = makeLayout(true, 10)

  local chat_header = makeLayout(false, 5)
  local chat_title_tv = makeText(getVerifiedName(target_user) .. " (Checking...)", 15)
  chat_title_tv.setTextColor(0xFF1E88E5)
  chat_header.addView(chat_title_tv, LinearLayout.LayoutParams(0, -2, 1))

  local more_btn = makeButton("More Options")
  chat_header.addView(more_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(chat_header)

  local block_notice_banner = makeText("", 13)
  block_notice_banner.setTextColor(0xFFD32F2F)
  block_notice_banner.setPadding(6, 6, 6, 6)
  block_notice_banner.setVisibility(View.GONE)
  layout.addView(block_notice_banner)

  local scroll = ScrollView(activity)
  local chat_container = makeLayout(true, 8)
  scroll.addView(chat_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 320))

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

  local voice_call_btn = makeButton("Voice Call")
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
    .setTitle(getVerifiedName(target_user))
    .setView(layout)
    .setCancelable(true)
    .create()

  dialog.show()

  local room_key = getSymmetricChatKey(current_username, target_user)
  local seen_message_ids = {}
  local is_chat_active = true
  local is_initial_load = true
  local chat_open_time = os.date("%Y%m%d%H%M%S")
  local last_rendered_data_hash = ""
  local live_handler = Handler(Looper.getMainLooper())
  local live_runnable = nil

  local is_blocked_by_them = false
  local is_blocked_by_me = false

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
        showToast("Voice message sent.")
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
    if not is_chat_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "user_presence/" .. encodeKey(target_user) .. ".json", function(s, r)
      if not is_chat_active then return end
      local base_name = getVerifiedName(target_user)
      if s and r and r ~= "null" then
        local ok, data = pcall(cjson.decode, r)
        if ok and type(data) == "table" then
          local current_time = os.time()
          local last_time = tonumber(data.time_epoch or 0)
          if data.status == "online" and (current_time - last_time < 180) then
            chat_title_tv.setText(base_name .. " (Online)")
            dialog.setTitle(base_name .. " (Online)")
          else
            local ls = tostring(data.last_seen or "Offline")
            chat_title_tv.setText(base_name .. " (" .. ls .. ")")
            dialog.setTitle(base_name .. " (" .. ls .. ")")
          end
          return
        end
      end
      chat_title_tv.setText(base_name .. " (Offline)")
      dialog.setTitle(base_name .. " (Offline)")
    end)
  end

  checkPeerBlockStatus()
  checkTargetPresence()

  local function loadMessages(force_refresh)
    if not is_chat_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "personal_chats/" .. room_key .. ".json", function(success, response)
      if not is_chat_active then return end
      local msg_list = {}
      local current_hash_builder = {}

      if success and response and response ~= "null" then
        local ok, data = pcall(cjson.decode, response)
        if ok and type(data) == "table" then
          for k, v in pairs(data) do
            if type(v) == "table" then
              v.id = k
              table.insert(msg_list, v)
              local base_msg_url = FIREBASE_URL .. "personal_chats/" .. room_key .. "/" .. k
              if normalizeUser(v.receiver or "") == normalizeUser(current_username) then
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
            if normalizeUser(m.sender or "") == normalizeUser(current_username) and normalizeUser(Uri.decode(tostring(rk))) ~= normalizeUser(current_username) then
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

      if new_reaction_on_my_msg and is_chat_active then
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
          if not is_initial_load and normalizeUser(m.sender or "") ~= normalizeUser(current_username) and tostring(m.timestamp_raw or "") > chat_open_time then
            new_incoming_msg = true
          end
        end
      end

      last_rendered_data_hash = current_data_hash
      chat_container.removeAllViews()
      local room_voice_playlist = {}

      if #msg_list == 0 then
        chat_container.addView(makeText("No messages yet. Say hello.", 14))
      else
        local last_day_header = ""
        for _, msg in ipairs(msg_list) do
          local day_lbl = getDayLabelFromRaw(msg.timestamp_raw)
          if day_lbl ~= "" and day_lbl ~= last_day_header then
            last_day_header = day_lbl
            chat_container.addView(createAccessibleDayHeader(day_lbl), LinearLayout.LayoutParams(-1, -2))
          end

          local is_me = (normalizeUser(msg.sender or "") == normalizeUser(current_username))
          local is_deleted_all = (msg.deleted_for_everyone == true or msg.deleted_for_everyone == "true")
          local bubble = makeLayout(true, 8)
          if is_me then
            bubble.setBackgroundColor(0xFFDCF8C6)
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
              quote_box.addView(makeText("Replying to " .. getVerifiedName(msg.reply_to.sender), 11))
              local q_preview = tostring(msg.reply_to.text or "")
              if #q_preview > 80 then q_preview = q_preview:sub(1, 80) .. "..." end
              local q_tv = makeText(q_preview, 12)
              q_tv.setTextColor(0xFF555555)
              quote_box.addView(q_tv)
              bubble.addView(quote_box, LinearLayout.LayoutParams(-1, -2))
            end

            local sender_label = is_me and "You" or getVerifiedName(msg.sender)
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
                        reply_text_preview.setText("Replying to " .. tostring(msg.sender or "") .. "\n" .. tostring(msg.text or ""))
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

      if new_incoming_msg and is_chat_active then
        playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)
      end
      is_initial_load = false
    end)
  end

  loadMessages(true)

  live_runnable = Runnable({
    run = function()
      if is_chat_active then
        syncServerAndRoomSettings(function()
          if is_chat_active then
            loadMessages(false)
            checkPeerBlockStatus()
            checkTargetPresence()
          end
        end)
        live_handler.postDelayed(live_runnable, CHAT_POLL_INTERVAL_MS)
      end
    end
  })
  live_handler.postDelayed(live_runnable, CHAT_POLL_INTERVAL_MS)

  more_btn.setOnClickListener(function()
    http_get(FIREBASE_URL .. "user_blocks/" .. encodeKey(current_username) .. "/" .. encodeKey(target_user) .. ".json", function(s_blk, r_blk)
      local currently_blocked = (s_blk and (r_blk == "true" or r_blk == '"true"'))
      local block_action_title = currently_blocked and "Unblock User" or "Block User"
      local choices = {"Clear Chat", block_action_title}

      AlertDialog.Builder(activity)
        .setTitle("More Options")
        .setItems(choices, DialogInterface.OnClickListener{
          onClick = function(d_choice, w)
            local selected = choices[w + 1]
            if selected == "Clear Chat" then
              http_delete(FIREBASE_URL .. "personal_chats/" .. room_key .. ".json", function(ok)
                if ok then
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
            end
          end
        }).show()
    end)
  end)

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
      else
        showToast("Failed to send message.")
      end
    end)
  end)
end

-- ========================================================
-- BTP VOICE ROOM (ONLINE COUNT + VOICE CHAT + ONE-TIME CUES + LOCK)
-- ========================================================

function openBtpVoiceRoomDialog()
  local layout = makeLayout(true, 10)

  local room_header = makeLayout(false, 5)
  local initial_lock_view = public_room_locked and not canBypassRoomLock(current_username)
  local initial_title = initial_lock_view and "BTP Voice Room" or "BTP Voice Room (1 online)"
  local title_tv = makeText(initial_title, 16)
  title_tv.setTextColor(0xFF1E88E5)
  room_header.addView(title_tv, LinearLayout.LayoutParams(0, -2, 1))

  local start_vc_btn = makeButton("Voice Chat")
  start_vc_btn.setContentDescription("Start Voice Chat")
  room_header.addView(start_vc_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(room_header)

  local one_time_cue_banner = makeText("", 12)
  one_time_cue_banner.setTextColor(0xFF0D47A1)
  one_time_cue_banner.setBackgroundColor(0xFFE3F2FD)
  one_time_cue_banner.setPadding(8, 6, 8, 6)
  one_time_cue_banner.setVisibility(View.GONE)
  layout.addView(one_time_cue_banner)

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

  start_vc_btn.setOnClickListener(function()
    startRoomVoiceChatSession("BTP Voice Room")
  end)

  dialog.setOnDismissListener(DialogInterface.OnDismissListener{ onDismiss = closeRoom })
  dialog.setOnCancelListener(DialogInterface.OnCancelListener{ onCancel = closeRoom })

  local function applyRoomLockAndOnlineState()
    if not is_room_active then return end
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

    if not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "user_presence.json", function(s, r)
      if not is_room_active or public_room_locked then return end
      local count = 1
      if s and r and r ~= "null" then
        local ok, data = pcall(cjson.decode, r)
        if ok and type(data) == "table" then
          count = 0
          local now = os.time()
          for _, p in pairs(data) do
            if type(p) == "table" and p.status == "online" and (now - tonumber(p.time_epoch or 0) < 180) then
              count = count + 1
            end
          end
          if count < 1 then count = 1 end
        end
      end
      local combined_title = "BTP Voice Room (" .. tostring(count) .. " online)"
      title_tv.setText(combined_title)
      dialog.setTitle(combined_title)
    end)
  end

  local function loadRoomMessages(force_refresh)
    if not is_room_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "btp_voice_room.json", function(success, response)
      if not is_room_active then return end
      local msg_list = {}
      local hash_builder = {}

      if success and response and response ~= "null" then
        local ok, data = pcall(cjson.decode, response)
        if ok and type(data) == "table" then
          for k, v in pairs(data) do
            if type(v) == "table" then
              v.id = k
              table.insert(msg_list, v)
              markMessageSeenInFirebase(FIREBASE_URL .. "btp_voice_room/" .. tostring(k))
            end
          end
        end
      end

      table.sort(msg_list, function(a, b)
        return tostring(a.timestamp_raw or a.timestamp or "") < tostring(b.timestamp_raw or b.timestamp or "")
      end)

      local one_time_notices = collectRoomOneTimeNotices(msg_list)
      if #one_time_notices > 0 then
        one_time_cue_banner.setText(table.concat(one_time_notices, "\n"))
        one_time_cue_banner.setVisibility(View.VISIBLE)
      end

      local new_rx_on_mine = false
      for _, m in ipairs(msg_list) do
        local r_pairs = {}
        if type(m.reactions) == "table" then
          for rk, rv in pairs(m.reactions) do
            table.insert(r_pairs, tostring(rk) .. "=" .. tostring(rv))
            local rx_unique = "vr_" .. tostring(m.id) .. "_" .. tostring(rk) .. "_" .. tostring(rv)
            if normalizeUser(m.sender or "") == normalizeUser(current_username) and normalizeUser(Uri.decode(tostring(rk))) ~= normalizeUser(current_username) then
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

      if new_rx_on_mine and is_room_active then
        playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
      end

      if cur_hash == last_hash and not is_initial_load and not force_refresh then return end
      if active_voice_player ~= nil and not force_refresh then return end

      local new_incoming = false
      for _, m in ipairs(msg_list) do
        if not seen_ids[m.id] then
          seen_ids[m.id] = true
          if not is_initial_load and normalizeUser(m.sender or "") ~= normalizeUser(current_username) and tostring(m.timestamp_raw or "") > room_open_time then
            new_incoming = true
          end
        end
      end

      last_hash = cur_hash
      chat_container.removeAllViews()
      local vr_playlist = {}

      if #msg_list == 0 then
        chat_container.addView(makeText("Welcome to BTP Voice Room. Start the conversation.", 14))
      else
        local last_day = ""
        for _, msg in ipairs(msg_list) do
          local dl = getDayLabelFromRaw(msg.timestamp_raw)
          if dl ~= "" and dl ~= last_day then
            last_day = dl
            chat_container.addView(createAccessibleDayHeader(dl), LinearLayout.LayoutParams(-1, -2))
          end

          local is_me = (normalizeUser(msg.sender or "") == normalizeUser(current_username))
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
              qbox.addView(makeText("Replying to " .. getVerifiedName(msg.reply_to.sender), 11))
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
                        reply_text_preview.setText("Replying to " .. tostring(msg.sender or "") .. "\n" .. tostring(msg.text or ""))
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
      if new_incoming and is_room_active then
        playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)
      end
      is_initial_load = false
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

  syncServerAndRoomSettings(function()
    if is_room_active then
      applyRoomLockAndOnlineState()
      loadRoomMessages(true)
    end
  end)

  live_runnable = Runnable({
    run = function()
      if is_room_active then
        syncServerAndRoomSettings(function()
          if is_room_active then
            applyRoomLockAndOnlineState()
            loadRoomMessages(false)
          end
        end)
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
-- GROUPS SYSTEM (24H DISAPPEARING MESSAGES + CLEAN JOIN & APPROVE FLOW + LOCK)
-- ========================================================

local function isGroupDisappear24hEnabled(group_data)
  return (type(group_data) == "table") and (group_data.disappear_24h == true or group_data.disappear_24h == "true")
end

local function isMessageExpired24h(msg_tbl, now_epoch)
  if type(msg_tbl) ~= "table" then return false end
  local m_ep = tonumber(msg_tbl.timestamp_epoch or 0)
  if m_ep > 0 then
    return (now_epoch - m_ep) >= DISAPPEAR_24H_SEC
  end
  return false
end

function showCreateGroupDialog(onCreatedCallback)
  local layout = makeLayout(true, 16)

  local name_input = EditText(activity)
  name_input.setHint("Enter Group Name (Required)")
  layout.addView(name_input)

  local desc_input = EditText(activity)
  desc_input.setHint("Group Description (Optional)")
  layout.addView(desc_input)

  local approval_required = false
  local approval_toggle_btn = makeButton("Join Mode: Direct Join")
  layout.addView(approval_toggle_btn)

  local disappear_24h_enabled = false
  local disappear_toggle_btn = makeButton("Disappearing Messages (24 Hours): OFF")
  layout.addView(disappear_toggle_btn)

  approval_toggle_btn.setOnClickListener(function()
    approval_required = not approval_required
    approval_toggle_btn.setText(approval_required and "Join Mode: Approval Required" or "Join Mode: Direct Join")
  end)

  disappear_toggle_btn.setOnClickListener(function()
    disappear_24h_enabled = not disappear_24h_enabled
    disappear_toggle_btn.setText(disappear_24h_enabled and "Disappearing Messages (24 Hours): ON" or "Disappearing Messages (24 Hours): OFF")
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
        disappear_24h = disappear_24h_enabled,
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
          showToast("Group created successfully.")
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
  local norm = normalizeUser(uname)
  if normalizeUser(group_data.creator or "") == norm then return true end
  if type(group_data.admins) == "table" then
    for k, v in pairs(group_data.admins) do
      if normalizeUser(Uri.decode(tostring(k))) == norm and (v == true or v == "true") then
        return true
      end
    end
  end
  return false
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

  local is_creator = (normalizeUser(group_data.creator or "") == normalizeUser(current_username))
  local is_admin = isUserGroupAdmin(group_data, current_username)

  inner.addView(makeText("Group Name: " .. tostring(group_data.name or ""), 16))
  inner.addView(makeText("Creator: " .. getVerifiedName(group_data.creator or ""), 13))
  inner.addView(makeText("Description: " .. (tostring(group_data.description or "") ~= "" and tostring(group_data.description) or "None"), 13))
  inner.addView(makeText("Members: " .. tostring(group_data.members and table_size(group_data.members) or 1), 13))
  inner.addView(makeText("Disappearing Messages (24h): " .. (isGroupDisappear24hEnabled(group_data) and "ON" or "OFF"), 13))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Group Info & Settings")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()
  dialog.show()

  if is_admin then
    inner.addView(makeText("Group Settings", 14))

    local desc_edit = EditText(activity)
    desc_edit.setHint("Edit Description")
    desc_edit.setText(tostring(group_data.description or ""))
    inner.addView(desc_edit)

    local save_desc_btn = makeButton("Save Description")
    inner.addView(save_desc_btn)

    save_desc_btn.setOnClickListener(function()
      local new_d = trim(desc_edit.getText())
      http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/description.json", "PUT", new_d, function(ok)
        if ok then
          group_data.description = new_d
          showToast("Description updated.")
        end
      end)
    end)

    local cur_disappear = isGroupDisappear24hEnabled(group_data)
    local disappear_btn = makeButton("Disappearing Messages (24 Hours): " .. (cur_disappear and "ON" or "OFF"))
    inner.addView(disappear_btn)

    disappear_btn.setOnClickListener(function()
      local next_d = not cur_disappear
      http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/disappear_24h.json", "PUT", next_d, function(ok)
        if ok then
          cur_disappear = next_d
          group_data.disappear_24h = next_d
          disappear_btn.setText("Disappearing Messages (24 Hours): " .. (cur_disappear and "ON" or "OFF"))
          showToast(cur_disappear and "24-hour disappearing messages enabled." or "24-hour disappearing messages disabled.")
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
      inner.addView(makeText("Pending Join Requests", 14))
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
              showToast(actual_req_user .. " approved.")
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

  inner.addView(makeText("Group Members", 14))
  if type(group_data.members) == "table" then
    for m_key, m_val in pairs(group_data.members) do
      local m_name = type(m_val) == "string" and m_val or Uri.decode(tostring(m_key))
      local m_is_admin = isUserGroupAdmin(group_data, m_name)
      local m_row = makeLayout(false, 4)
      m_row.addView(makeText(getVerifiedName(m_name) .. (m_is_admin and " (Admin)" or ""), 13), LinearLayout.LayoutParams(0, -2, 1))

      if is_creator and normalizeUser(m_name) ~= normalizeUser(current_username) then
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
              showToast(m_name .. " is now Group Admin.")
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
  local title_tv = makeText(initial_gname, 15)
  title_tv.setTextColor(0xFF1E88E5)
  g_header.addView(title_tv, LinearLayout.LayoutParams(0, -2, 1))

  local more_btn = makeButton("More Options")
  g_header.addView(more_btn, LinearLayout.LayoutParams(-2, -2))
  layout.addView(g_header)

  local perm_banner = makeText("Only admin can send messages", 13)
  perm_banner.setTextColor(0xFFD32F2F)
  perm_banner.setPadding(6, 4, 6, 4)
  perm_banner.setVisibility(View.GONE)
  layout.addView(perm_banner)

  local scroll = ScrollView(activity)
  local chat_container = makeLayout(true, 8)
  scroll.addView(chat_container)
  layout.addView(scroll, LinearLayout.LayoutParams(-1, 320))

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

  local group_voice_call_btn = makeButton("Group Voice Call")
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
    .setTitle(initial_gname)
    .setView(layout)
    .setCancelable(true)
    .create()
  dialog.show()

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

        title_tv.setText(gname_str)
        dialog.setTitle(gname_str)
      end
    end)
  end

  local function touchGroupActivity()
    http_post_or_put(FIREBASE_URL .. "btp_groups/" .. gid .. "/last_activity_epoch.json", "PUT", os.time(), function() end)
  end

  local function loadGroupMessages(force_refresh)
    if not is_grp_active or not isNetworkAvailable() then return end
    http_get(FIREBASE_URL .. "btp_group_messages/" .. gid .. ".json", function(success, response)
      if not is_grp_active then return end
      local msg_list = {}
      local hash_builder = {}
      local now_ep = os.time()
      local expire_24h = isGroupDisappear24hEnabled(group_data)

      if success and response and response ~= "null" then
        local ok, data = pcall(cjson.decode, response)
        if ok and type(data) == "table" then
          for k, v in pairs(data) do
            if type(v) == "table" then
              if expire_24h and isMessageExpired24h(v, now_ep) then
                http_delete(FIREBASE_URL .. "btp_group_messages/" .. gid .. "/" .. tostring(k) .. ".json", function() end)
              else
                local traw = tostring(v.timestamp_raw or "")
                if local_cleared_before == "" or traw > local_cleared_before then
                  v.id = k
                  table.insert(msg_list, v)
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
            if normalizeUser(m.sender or "") == normalizeUser(current_username) and normalizeUser(Uri.decode(tostring(rk))) ~= normalizeUser(current_username) then
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
      local cur_hash = table.concat(hash_builder, "|") .. ":" .. local_cleared_before

      if new_rx_on_mine and is_grp_active then
        playSound(SOUND_REACTION, nil, ToneGenerator.TONE_PROP_BEEP, false)
      end

      if cur_hash == last_hash and not is_initial_load and not force_refresh then return end
      if active_voice_player ~= nil and not force_refresh then return end

      local new_incoming = false
      for _, m in ipairs(msg_list) do
        if not seen_ids[m.id] then
          seen_ids[m.id] = true
          if not is_initial_load and normalizeUser(m.sender or "") ~= normalizeUser(current_username) and tostring(m.timestamp_raw or "") > grp_open_time then
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

          local is_me = (normalizeUser(msg.sender or "") == normalizeUser(current_username))
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
              qbox.addView(makeText("Replying to " .. getVerifiedName(msg.reply_to.sender), 11))
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
                        reply_text_preview.setText("Replying to " .. tostring(msg.sender or "") .. "\n" .. tostring(msg.text or ""))
                        reply_banner.setVisibility(View.VISIBLE)
                        msg_input.requestFocus()
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
      if new_incoming and is_grp_active then
        playSound(SOUND_RECEIVE, nil, ToneGenerator.TONE_PROP_BEEP, false)
      end
      is_initial_load = false
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
      timestamp_raw = os.date("%Y%m%d%H%M%S"),
      timestamp_epoch = os.time()
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
    local is_creator = (normalizeUser(group_data.creator or "") == normalizeUser(current_username))
    local choices = {"Group Info & Settings", "Clear Chat (For Me)", "Delete / Hide Group (For Me)"}
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
      if is_grp_active then
        syncServerAndRoomSettings(function()
          if is_grp_active then
            refreshGroupMetaAndOnline()
            loadGroupMessages(false)
          end
        end)
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
      timestamp_raw = os.date("%Y%m%d%H%M%S"),
      timestamp_epoch = os.time()
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

  list_container.addView(makeText("Loading groups...", 14))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Groups")
    .setView(layout)
    .setPositiveButton("Close", nil)
    .create()
  dialog.show()

  local function loadAllGroups()
    http_get(FIREBASE_URL .. "btp_groups.json", function(s_g, r_g)
      list_container.removeAllViews()
      local hidden_map = getLocalHiddenMap("hidden_groups_json")

      local groups_arr = {}
      if s_g and r_g and r_g ~= "null" then
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
        list_container.addView(makeText("No groups created yet. Tap Create Group to start one.", 14))
        return
      end

      local my_norm = normalizeUser(current_username)

      for _, g in ipairs(groups_arr) do
        local card = makeLayout(true, 10)
        card.setBackgroundColor(0xFFEEEEEE)
        card.setPadding(12, 10, 12, 10)
        card.setFocusable(true)
        card.setClickable(true)

        local is_banned_g = (g.is_banned == true or g.is_banned == "true")
        local is_member = false
        local is_pending = false

        if type(g.members) == "table" then
          for mk, mv in pairs(g.members) do
            local mname = type(mv) == "string" and mv or Uri.decode(tostring(mk))
            if normalizeUser(mname) == my_norm then
              is_member = true
            end
          end
        end

        if type(g.join_requests) == "table" then
          for rk, rv in pairs(g.join_requests) do
            local rname = type(rv) == "string" and rv or Uri.decode(tostring(rk))
            if normalizeUser(rname) == my_norm then
              is_pending = true
            end
          end
        end

        local gname_clean = tostring(g.name or "Unnamed Group")
        local gtitle = makeText(gname_clean, 16)
        gtitle.setTextColor(is_banned_g and 0xFFD32F2F or 0xFF1E88E5)
        card.addView(gtitle)

        local desc_txt = trim(tostring(g.description or ""))
        if desc_txt ~= "" then
          card.addView(makeText(desc_txt, 12))
        end

        local mem_cnt = g.members and table_size(g.members) or 1
        local detail_tv = makeText("Members: " .. tostring(mem_cnt), 12)
        detail_tv.setVisibility(View.GONE)
        card.addView(detail_tv)

        local join_btn
        if is_banned_g and not isVerifiedUser(current_username) then
          join_btn = makeButton("Exit Group")
        elseif is_member or isVerifiedUser(current_username) then
          join_btn = makeButton("Open Group")
        elseif is_pending then
          join_btn = makeButton("Request Pending")
          join_btn.setEnabled(false)
        elseif g.approval_required == true or g.approval_required == "true" then
          join_btn = makeButton("Request to Join")
        else
          join_btn = makeButton("Join")
        end
        join_btn.setVisibility(View.GONE)
        card.addView(join_btn, LinearLayout.LayoutParams(-1, -2))

        local function revealGroupDetailsAndJoin()
          detail_tv.setText("Members: " .. tostring(mem_cnt))
          detail_tv.setVisibility(View.VISIBLE)
          join_btn.setVisibility(View.VISIBLE)
        end

        card.setOnClickListener(function()
          revealGroupDetailsAndJoin()
        end)

        join_btn.setOnClickListener(function()
          if is_banned_g and not isVerifiedUser(current_username) then
            dialog.dismiss()
            showBannedGroupDialog(g.id, g, function()
              showGroupsListDialog()
            end)
          elseif is_member or isVerifiedUser(current_username) then
            dialog.dismiss()
            openGroupChatDialog(g.id, g)
          elseif g.approval_required == true or g.approval_required == "true" then
            http_post_or_put(FIREBASE_URL .. "btp_groups/" .. g.id .. "/join_requests/" .. encodeKey(current_username) .. ".json", "PUT", current_username, function(ok)
              if ok then
                showToast("Join request sent.")
                loadAllGroups()
              end
            end)
          else
            http_post_or_put(FIREBASE_URL .. "btp_groups/" .. g.id .. "/members/" .. encodeKey(current_username) .. ".json", "PUT", current_username, function(ok)
              if ok then
                if not g.members then g.members = {} end
                g.members[encodeKey(current_username)] = current_username
                showToast("Joined group.")
                dialog.dismiss()
                openGroupChatDialog(g.id, g)
              end
            end)
          end
        end)

        list_container.addView(card, LinearLayout.LayoutParams(-1, -2))
      end
    end)
  end

  create_grp_btn.setOnClickListener(function()
    showCreateGroupDialog(function()
      loadAllGroups()
    end)
  end)

  loadAllGroups()
end

-- ========================================================
-- CHAT HUB (MORE OPTIONS -> BTP ASSISTANT -> BTP VOICE ROOM -> VIEW GROUPS -> DIRECT CHATS)
-- ========================================================

function showResourceChatDialog()
  local layout = makeLayout(true, 15)

  local top_actions = makeLayout(false, 4)
  local more_chat_btn = makeButton("More Options (Create Group)")
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

  users_container.addView(makeText("Loading chats...", 14))

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
    local opts = {"Create New Group", "View All Groups"}
    AlertDialog.Builder(activity)
      .setTitle("More Options")
      .setItems(opts, DialogInterface.OnClickListener{
        onClick = function(d, w)
          if w == 0 then
            showCreateGroupDialog(function()
              dialog.dismiss()
              showGroupsListDialog()
            end)
          else
            dialog.dismiss()
            showGroupsListDialog()
          end
        end
      }).show()
  end)

  syncServerAndRoomSettings(function()
    http_get(FIREBASE_URL .. "registered_users.json", function(s_reg, r_reg)
      http_get(FIREBASE_URL .. "personal_chats.json", function(s_chats, r_chats)
        http_get(FIREBASE_URL .. "user_presence.json", function(s_pres, r_pres)
          users_container.removeAllViews()

          local online_total = 1
          if s_pres and r_pres and r_pres ~= "null" then
            local ok_p, pdata = pcall(cjson.decode, r_pres)
            if ok_p and type(pdata) == "table" then
              online_total = 0
              local now = os.time()
              for _, p in pairs(pdata) do
                if type(p) == "table" and p.status == "online" and (now - tonumber(p.time_epoch or 0) < 180) then
                  online_total = online_total + 1
                end
              end
              if online_total < 1 then online_total = 1 end
            end
          end

          -- 1. Pinned Top Card: BTP Voice Room
          local voice_room_card = makeLayout(true, 12)
          voice_room_card.setBackgroundColor(0xFFE3F2FD)
          local vr_title_str = "BTP Voice Room (" .. tostring(online_total) .. " online)"
          if public_room_locked and not canBypassRoomLock(current_username) then
            vr_title_str = "BTP Voice Room"
          elseif public_room_locked then
            vr_title_str = vr_title_str .. " • Locked"
          end
          local vr_title = makeText(vr_title_str, 16)
          vr_title.setTextColor(0xFF0D47A1)
          voice_room_card.addView(vr_title)
          voice_room_card.addView(makeText("Public voice and text room for all members", 12))
          users_container.addView(voice_room_card, LinearLayout.LayoutParams(-1, -2))

          voice_room_card.setOnClickListener(function()
            dialog.dismiss()
            openBtpVoiceRoomDialog()
          end)

          -- 2. Pinned Second Card: View Groups
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

          -- 3. Personal Direct Chats List
          local user_map = {}
          local user_last_msg_time = {}
          local user_last_msg_data = {}
          local user_unread_count = {}

          if s_reg and r_reg and r_reg ~= "null" then
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

          if s_chats and r_chats and r_chats ~= "null" then
            local ok, chats_data = pcall(cjson.decode, r_chats)
            if ok and type(chats_data) == "table" then
              for rkey, msgs in pairs(chats_data) do
                if type(msgs) == "table" then
                  for mid, m in pairs(msgs) do
                    if type(m) == "table" then
                      local other_u = nil
                      if normalizeUser(m.sender or "") == normalizeUser(current_username) then
                        other_u = m.receiver
                      elseif normalizeUser(m.receiver or "") == normalizeUser(current_username) then
                        other_u = m.sender
                      end
                      
                      if other_u and other_u ~= "" then
                        if not user_map[other_u] then user_map[other_u] = 0 end
                        if normalizeUser(m.receiver or "") == normalizeUser(current_username) and m.status ~= "Read" then
                          user_unread_count[other_u] = (user_unread_count[other_u] or 0) + 1
                        end

                        local t_raw = tostring(m.timestamp_raw or "0")
                        if not user_last_msg_time[other_u] or t_raw > user_last_msg_time[other_u] then
                          user_last_msg_time[other_u] = t_raw
                          user_last_msg_data[other_u] = m
                        end
                      end
                    end
                  end
                end
              end
            end
          end

          local user_list = {}
          for u, _ in pairs(user_map) do
            if normalizeUser(u) ~= normalizeUser(current_username) then
              table.insert(user_list, u)
            end
          end

          table.sort(user_list, function(a, b)
            local ta = user_last_msg_time[a] or ""
            local tb = user_last_msg_time[b] or ""
            if ta ~= tb then return ta > tb end
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

            local last_m = user_last_msg_data[u]
            local unread = user_unread_count[u] or 0

            local top_row = makeLayout(false, 0)
            local name_tv = makeText(getVerifiedName(u), 16)
            name_tv.setTextColor(0xFF1E88E5)
            top_row.addView(name_tv, LinearLayout.LayoutParams(0, -2, 1))

            if last_m then
              local time_text = getWhatsAppListTime(last_m.timestamp_raw, last_m.timestamp)
              local time_tv = makeText(time_text, 12)
              time_tv.setTextColor(0xFF777777)
              top_row.addView(time_tv, LinearLayout.LayoutParams(-2, -2))
            end
            card.addView(top_row)

            local notif_parts = {}
            if unread > 0 then
              table.insert(notif_parts, tostring(unread) .. " new message" .. (unread > 1 and "s" or ""))
            end

            local is_reply_to_me = false
            if last_m and normalizeUser(last_m.sender or "") ~= normalizeUser(current_username) and last_m.reply_to and type(last_m.reply_to) == "table" then
              local rep_sender = normalizeUser(last_m.reply_to.sender or "")
              if rep_sender == normalizeUser(current_username) then
                is_reply_to_me = true
              end
            end

            local is_mentioned = false
            if last_m and normalizeUser(last_m.sender or "") ~= normalizeUser(current_username) and last_m.text then
              local txt_lower = tostring(last_m.text):lower()
              local my_name_lower = normalizeUser(current_username)
              if my_name_lower ~= "" and (txt_lower:find("@" .. my_name_lower, 1, true) or txt_lower:find(my_name_lower, 1, true)) then
                is_mentioned = true
              end
            end

            if unread > 0 then
              if is_reply_to_me and is_mentioned then
                table.insert(notif_parts, "Replied and mentioned you")
              elseif is_reply_to_me then
                table.insert(notif_parts, "Replied to your message")
              elseif is_mentioned then
                table.insert(notif_parts, "Mentioned you")
              end
            end

            if #notif_parts > 0 then
              local notif_line = makeText(table.concat(notif_parts, " • "), 12)
              notif_line.setTextColor(0xFFD32F2F)
              notif_line.setPadding(0, 2, 0, 2)
              card.addView(notif_line)
            end

            if last_m then
              local sender_tag = ""
              if normalizeUser(last_m.sender or "") == normalizeUser(current_username) then
                sender_tag = "You: "
              else
                sender_tag = tostring(last_m.sender or "") .. ": "
              end
              local preview_txt = tostring(last_m.text or "")
              if last_m.deleted_for_everyone == true or last_m.deleted_for_everyone == "true" then
                preview_txt = "This message was deleted"
              elseif last_m.msg_type == "voice" then
                preview_txt = "Voice message (" .. tostring(last_m.audio_duration or "0") .. "s)"
              elseif #preview_txt > 70 then
                preview_txt = preview_txt:sub(1, 70) .. "..."
              end
              local msg_preview_tv = makeText(sender_tag .. preview_txt, 13)
              msg_preview_tv.setTextColor(0xFF444444)
              card.addView(msg_preview_tv)
            else
              local no_msg_tv = makeText("No messages yet. Tap to start chat.", 12)
              no_msg_tv.setTextColor(0xFF888888)
              card.addView(no_msg_tv)
            end

            users_container.addView(card, LinearLayout.LayoutParams(-1, -2))

            card.setOnClickListener(function()
              dialog.dismiss()
              openPersonalChat(u)
            end)
          end
        end)
      end)
    end)
  end)
end

-- ========================================================
-- ABOUT CODE DIALOG (WITH LIKED ALONG WITH SUMMARY & SOUND)
-- ========================================================

local function formatCodeLikesSummary(likes_tbl)
  if type(likes_tbl) ~= "table" or table_size(likes_tbl) == 0 then
    return "0 Likes"
  end
  local names = {}
  for lk, _ in pairs(likes_tbl) do
    table.insert(names, Uri.decode(tostring(lk)))
  end
  local total = #names
  if total == 1 then
    return "Liked by " .. names[1]
  elseif total == 2 then
    return "Liked by " .. names[1] .. " along with 1 other person"
  else
    return "Liked by " .. names[1] .. " along with " .. tostring(total - 1) .. " other people"
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

  local copy_button = makeButton("Copy Code")
  inner.addView(copy_button)

  local like_button = makeButton("Like Code")
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

  like_button.setOnClickListener(function()
    if not item.id then return end
    local key = encodeKey(current_username)
    local url = FIREBASE_URL .. "codes/" .. item.id .. "/likes/" .. key .. ".json"
    http_post_or_put(url, "PUT", true, function(ok)
      if ok then
        playSound(SOUND_LIKE, nil, ToneGenerator.TONE_PROP_ACK, false)
        showToast("Liked.")
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
-- CODES FEED VIEW (HOME - RECENT CODES ALWAYS AT TOP)
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
    card.addView(makeText(formatCodeLikesSummary(item.likes), 12))

    local preview = item.code or ""
    if #preview > 250 then preview = preview:sub(1, 250) .. "\n\nPreview shortened" end
    local preview_view = makeText("Code Preview:\n" .. preview, 12)
    preview_view.setTextIsSelectable(true)
    card.addView(preview_view)

    local btn_row = makeLayout(false, 4)
    local copy_btn = makeButton("Copy Code")
    local details_btn = makeButton("View / Comment")

    btn_row.addView(copy_btn, LinearLayout.LayoutParams(0, -2, 1))
    btn_row.addView(details_btn, LinearLayout.LayoutParams(0, -2, 1))
    card.addView(btn_row)

    copy_btn.setOnClickListener(function()
      playSound(SOUND_CODE_HIT, nil, ToneGenerator.TONE_PROP_BEEP, false)
      copyCode(item.code or "")
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

function loadCodesData()
  if not isNetworkAvailable() then return end
  http_get(FIREBASE_URL .. "codes.json", function(success, response)
    all_codes_data = {}
    if success and response and response ~= "null" then
      local ok, data = pcall(cjson.decode, response)
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
-- UPLOAD CODE POPUP
-- ========================================================

function showUploadCodeDialog()
  local layout = makeLayout(true, 15)

  local title_input = EditText(activity)
  title_input.setHint("Enter Code Title")
  layout.addView(title_input)

  local desc_input = EditText(activity)
  desc_input.setHint("Enter Description")
  layout.addView(desc_input)

  local code_input = EditText(activity)
  code_input.setHint("Paste full Lua source code here...")
  code_input.setMinLines(7)
  code_input.setGravity(Gravity.TOP)
  layout.addView(code_input, LinearLayout.LayoutParams(-1, 0, 1))

  local dialog = AlertDialog.Builder(activity)
    .setTitle("Upload Open Source Code")
    .setView(layout)
    .setPositiveButton("Publish", nil)
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

      playLimitedSound(SOUND_UPLOAD, 3000)

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
          showToast("Code uploaded successfully.")
          dialog.dismiss()
          loadCodesData()
          if my_container then loadMyUploadsData() end
        else
          showToast("Upload failed. Check network.")
        end
      end)
    end
  })
end

-- ========================================================
-- MY CODES VIEW
-- ========================================================

local my_container

function loadMyUploadsData()
  if not my_container or not isNetworkAvailable() then return end
  my_container.removeAllViews()
  my_container.addView(makeText("Loading your uploaded codes...", 14))

  http_get(FIREBASE_URL .. "codes.json", function(success, response)
    my_container.removeAllViews()
    local my_list = {}
    local my_name_norm = normalizeUser(current_username)

    if success and response and response ~= "null" then
      local ok, data = pcall(cjson.decode, response)
      if ok and type(data) == "table" then
        for k, v in pairs(data) do
          if type(v) == "table" then
            local auth_norm = normalizeUser(v.author or "")
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

        local btn_row = makeLayout(false, 4)
        local view_btn = makeButton("View Code")
        local del_btn = makeButton("Delete Code")
        btn_row.addView(view_btn, LinearLayout.LayoutParams(0, -2, 1))
        btn_row.addView(del_btn, LinearLayout.LayoutParams(0, -2, 1))
        card.addView(btn_row)

        my_container.addView(card, LinearLayout.LayoutParams(-1, -2))

        view_btn.setOnClickListener(function()
          showAboutCodeDialog(v)
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
-- GROUP MANAGEMENT DIALOG (VERIFIED ONLY BAN / UNBAN / DELETE)
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
        card.addView(makeText("Group: " .. tostring(g.name or "Unnamed") .. (is_b and " - Banned" or " - Active"), 15))
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
-- USER ROLE INSPECTOR DIALOG (CLICK USER TO VIEW ROLE, STATUS & MANAGE)
-- ========================================================

local function openUserRoleDetailsDialog(target_uname, onChangedCallback)
  local is_ver = isVerifiedUser(target_uname)
  local is_adm = isAdminUser(target_uname)
  local is_blk = isUserBlockedGlobal(target_uname)

  local box = makeLayout(true, 14)
  box.addView(makeText("User: " .. tostring(target_uname), 17))
  box.addView(makeText("Role: " .. (is_ver and "Verified" or (is_adm and "Admin" or "Normal")), 14))
  box.addView(makeText("Status: " .. (is_blk and "Blocked" or "Active"), 14))

  local dlg = AlertDialog.Builder(activity)
    .setTitle("User Role & Status")
    .setView(box)
    .setPositiveButton("Close", nil)
    .create()

  local make_ver_btn = makeButton(is_ver and "Remove Verified" or "Make Verified")
  local make_adm_btn = makeButton(is_adm and "Remove Admin" or "Make Admin")
  local block_btn = makeButton(is_blk and "Unblock User" or "Block User")

  box.addView(make_ver_btn)
  box.addView(make_adm_btn)
  box.addView(block_btn)

  make_ver_btn.setOnClickListener(function()
    if is_ver then
      if isDeveloper(target_uname) then
        showToast("Primary developer cannot be unverified.")
        return
      end
      http_delete(FIREBASE_URL .. "verified_users/" .. encodeKey(target_uname) .. ".json", function()
        showToast(target_uname .. " is now unverified.")
        dlg.dismiss()
        if onChangedCallback then onChangedCallback() end
      end)
    else
      http_post_or_put(FIREBASE_URL .. "verified_users/" .. encodeKey(target_uname) .. ".json", "PUT", true, function()
        showToast(target_uname .. " is now Verified.")
        dlg.dismiss()
        if onChangedCallback then onChangedCallback() end
      end)
    end
  end)

  make_adm_btn.setOnClickListener(function()
    if is_adm then
      http_delete(FIREBASE_URL .. "admin_users/" .. encodeKey(target_uname) .. ".json", function()
        showToast(target_uname .. " removed from Admin.")
        dlg.dismiss()
        if onChangedCallback then onChangedCallback() end
      end)
    else
      http_post_or_put(FIREBASE_URL .. "admin_users/" .. encodeKey(target_uname) .. ".json", "PUT", true, function()
        showToast(target_uname .. " is now Admin.")
        dlg.dismiss()
        if onChangedCallback then onChangedCallback() end
      end)
    end
  end)

  block_btn.setOnClickListener(function()
    if is_blk then
      http_delete(FIREBASE_URL .. "blocked/" .. encodeKey(target_uname) .. ".json", function()
        http_delete(FIREBASE_URL .. "unblock_requests/" .. encodeKey(target_uname) .. ".json", function() end)
        showToast(target_uname .. " unblocked.")
        dlg.dismiss()
        if onChangedCallback then onChangedCallback() end
      end)
    else
      if isDeveloper(target_uname) then
        showToast("Primary developer cannot be blocked.")
        return
      end
      http_post_or_put(FIREBASE_URL .. "blocked/" .. encodeKey(target_uname) .. ".json", "PUT", true, function()
        showToast(target_uname .. " blocked.")
        dlg.dismiss()
        if onChangedCallback then onChangedCallback() end
      end)
    end
  end)

  dlg.show()
end

-- ========================================================
-- ADMIN PANEL DIALOG (FULL FOR VERIFIED/DEV, BROADCAST ONLY FOR ADMIN)
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
                showToast("Broadcast sent.")
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
    local assistant_mgmt_btn = makeButton("Assistant Management (Lock, Train & Feedback)")
    local group_mgmt_btn = makeButton("Group Management (Ban / Unban / Delete)")
    local lock_room_btn = makeButton(public_room_locked and "Unlock BTP Voice Room (Currently Locked)" or "Lock BTP Voice Room (Only Admin/Dev)")
    local server_toggle_btn = makeButton(server_is_down and "Turn Server ON (Currently Server OFF)" or "Turn Server OFF (Maintenance Mode)")
    local popup_note_btn = makeButton("Update Popup Announcement Note")
    local users_mgmt_btn = makeButton("Manage Users (Search, Role, Verified & Block)")
    local blocked_users_btn = makeButton("View Blocked Users & Unblock Requests")

    layout.addView(assistant_mgmt_btn)
    layout.addView(group_mgmt_btn)
    layout.addView(lock_room_btn)
    layout.addView(server_toggle_btn)
    layout.addView(popup_note_btn)
    layout.addView(users_mgmt_btn)
    layout.addView(blocked_users_btn)

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
                  showToast("Popup announcement note published.")
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
      local search_box = EditText(activity)
      search_box.setHint("Search user by name...")
      search_box.setContentDescription("Search user")
      u_layout.addView(search_box)

      local u_scroll = ScrollView(activity)
      local u_container = makeLayout(true, 8)
      u_scroll.addView(u_container)
      u_layout.addView(u_scroll, LinearLayout.LayoutParams(-1, 500))

      u_container.addView(makeText("Loading users...", 14))

      local u_dialog = AlertDialog.Builder(activity)
        .setTitle("Manage Users")
        .setView(u_layout)
        .setPositiveButton("Close", nil)
        .create()

      u_dialog.show()

      local master_names = {}

      local function renderUsersList(query_str)
        u_container.removeAllViews()
        local q = trim(tostring(query_str or "")):lower()

        local matched = {}
        local rest = {}
        for _, actual_name in ipairs(master_names) do
          local lname = tostring(actual_name):lower()
          if q ~= "" and lname:find(q, 1, true) then
            table.insert(matched, actual_name)
          else
            table.insert(rest, actual_name)
          end
        end

        local ordered = {}
        for _, m_name in ipairs(matched) do table.insert(ordered, m_name) end
        for _, r_name in ipairs(rest) do table.insert(ordered, r_name) end

        if #ordered == 0 then
          u_container.addView(makeText("No registered users found.", 14))
          return
        end

        for _, actual_name in ipairs(ordered) do
          local is_ver = isVerifiedUser(actual_name)
          local is_adm = isAdminUser(actual_name)
          local is_blocked = isUserBlockedGlobal(actual_name)

          local row = makeLayout(true, 10)
          row.setBackgroundColor(is_blocked and 0xFFFFCDD2 or 0xFFEEEEEE)
          row.setFocusable(true)
          row.setClickable(true)

          local name_tv = makeText(tostring(actual_name), 15)
          name_tv.setTextColor(0xFF1E88E5)
          row.addView(name_tv)

          local status_tv = makeText(getUserRoleStatusText(actual_name), 12)
          row.addView(status_tv)

          row.setOnClickListener(function()
            openUserRoleDetailsDialog(actual_name, function()
              loadVerifiedUsers(function()
                loadAdminUsers(function()
                  loadBlockedUsers(function()
                    renderUsersList(tostring(search_box.getText()))
                  end)
                end)
              end)
            end)
          end)

          u_container.addView(row, LinearLayout.LayoutParams(-1, -2))
        end
      end

      local function refreshUsersData()
        http_get(FIREBASE_URL .. "registered_users.json", function(s, r)
          loadVerifiedUsers(function()
            loadAdminUsers(function()
              loadBlockedUsers(function()
                master_names = {}
                local seen_norm = {}

                if s and r and r ~= "null" then
                  local ok, data = pcall(cjson.decode, r)
                  if ok and type(data) == "table" then
                    for uname, uinfo in pairs(data) do
                      local actual_name = trim(tostring((type(uinfo) == "table" and uinfo.username) or uname))
                      local nk = normalizeUser(actual_name)
                      if actual_name ~= "" and not seen_norm[nk] then
                        seen_norm[nk] = true
                        table.insert(master_names, actual_name)
                      end
                    end
                  end
                end

                if not seen_norm["ibrahim ansari"] then
                  table.insert(master_names, "Ibrahim Ansari")
                end

                table.sort(master_names, function(a, b)
                  return tostring(a):lower() < tostring(b):lower()
                end)

                renderUsersList(tostring(search_box.getText()))
              end)
            end)
          end)
        end)
      end

      search_box.addTextChangedListener({
        onTextChanged = function(s)
          renderUsersList(tostring(s))
        end
      })

      refreshUsersData()
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

  local notif_toggle_btn = makeButton("Background Notifications: " .. (notif_sound_status and "ENABLED ON" or "DISABLED OFF"))
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
    notif_toggle_btn.setText("Background Notifications: " .. (new_val and "ENABLED ON" or "DISABLED OFF"))
    if new_val then
      startBackgroundNotificationWatcher()
      showToast("Background notification enabled.")
    else
      stopBackgroundNotificationWatcher()
      showToast("Background notification turned off.")
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
-- SETTINGS VIEW (ADMIN PANEL FOR VERIFIED & ADMIN USERS + CHECK FOR UPDATE)
-- ========================================================

function createSettingsView()
  local layout = makeLayout(true, 20)

  local change_name = makeButton("Change Username")
  layout.addView(change_name)

  local more_options_btn = makeButton("More Options (Create Group & Groups)")
  layout.addView(more_options_btn)

  more_options_btn.setOnClickListener(function()
    local opts = {"Create New Group", "View All Groups"}
    AlertDialog.Builder(activity)
      .setTitle("More Options")
      .setItems(opts, DialogInterface.OnClickListener{
        onClick = function(d, w)
          if w == 0 then
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

  local check_update_btn = makeButton("Check for Update")
  layout.addView(check_update_btn)

  check_update_btn.setOnClickListener(function()
    checkForAppUpdate(true)
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
    showMessage(
      "About This App",
      APP_TITLE .. "\n" .. APP_DEV .. "\nVersion: " .. APP_VERSION .. "\n\n"
      .. "A fast, accessible community and code-sharing hub built for creators and developers. "
      .. "Includes BTP Assistant for smart Q&A and code help, BTP Voice Room with voice chat, "
      .. "community groups with 24-hour disappearing messages, direct chats with voice messages and calls, "
      .. "and clean screen-reader support."
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

  local dev_label = makeText(APP_DEV .. " • v" .. APP_VERSION, 13)
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
-- LIFECYCLE HOOKS: ZERO BACKGROUND RUNTIME OUTSIDE APP
-- ========================================================

function onStop()
  stopActiveVoicePlayer(false)
  stopBackgroundNotificationWatcher()
  resetCallAudioMode()
  if presence_handler and presence_runnable then
    pcall(function() presence_handler.removeCallbacks(presence_runnable) end)
    presence_handler = nil
    presence_runnable = nil
  end
end

function onDestroy()
  stopActiveVoicePlayer(false)
  stopBackgroundNotificationWatcher()
  resetCallAudioMode()
  if incoming_call_handler and incoming_call_runnable then
    pcall(function() incoming_call_handler.removeCallbacks(incoming_call_runnable) end)
    incoming_call_handler = nil
    incoming_call_runnable = nil
  end
  if presence_handler and presence_runnable then
    pcall(function() presence_handler.removeCallbacks(presence_runnable) end)
    presence_handler = nil
    presence_runnable = nil
  end
  updatePresence("offline")
end

-- ========================================================
-- STARTUP SEQUENCE (ZERO HANG - ASYNC INIT)
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
            checkForAppUpdate(false)
          end)
        end)
      end)
    end)
  end)

  local cleanup_handler = Handler(Looper.getMainLooper())
  cleanup_handler.postDelayed(Runnable({
    run = function()
      runSilentAutoCleanup()
    end
  }), 15000)
end
