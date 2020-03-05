let () =
  Guedra.reg_client
    ~ppi:!Drive.ppi
    ~font_name:!Drive.font_name
    ~font_size:!Drive.font_size
    Syncstitch.start;
  Drive.drive Drive.RunModeProcessExplorer
