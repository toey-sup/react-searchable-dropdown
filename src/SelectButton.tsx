import Tooltip from '@material-ui/core/Tooltip';
import Typography from '@material-ui/core/Typography';
import ExpandMoreIcon from '@material-ui/icons/ExpandMore';

interface SelectButtonProps {
  tooltip?: string;
  label: string;
  id?: string;
  selectDivClassName?: string;
  selectDivPropsStyle?: React.CSSProperties;
  disable?: boolean;
  placeholder?: string;
  dropDownArrowClassName?: string;
  dropDownArrowComponent?: React.ReactNode;
  open?: boolean;
  error?: boolean;
  setOpen: (value: boolean) => void;
}

const SelectButton: React.FC<SelectButtonProps> = ({
  id,
  tooltip,
  label,
  selectDivClassName,
  disable,
  selectDivPropsStyle,
  placeholder,
  open,
  error,
  dropDownArrowClassName,
  dropDownArrowComponent,
  setOpen,
}) => {
  return (
    <Tooltip
      title={tooltip ?? label ?? ''}
      key={tooltip ?? label}
      enterDelay={800}
      enterNextDelay={500}
      interactive
      placement="top"
      arrow
    >
      <button
        type="button"
        className={`flex items-center border px-4 rounded py-1 hover:border-gray-400 w-full h-full ${
          open ? 'border-gray-400' : ''
        } ${error ? 'border-red-400' : ''} ${selectDivClassName || ''} ${disable ? 'bg-gray-200' : ''}`}
        style={selectDivPropsStyle}
        onClick={() => setOpen(true)}
        id={`${id}-select-button`}
        disabled={disable}
      >
        <div className={`w-full flex pr-5`}>
          {label ? (
            <Typography variant="body1" noWrap style={{...disable ? { color: 'transparent'} : {}}}>
              {label}
            </Typography>
          ) : (
            <Typography variant="body1" style={{ fontStyle: 'italic', color: disable ? 'transparent' : 'gray' }}>
              {placeholder}
            </Typography>
          )}
        </div>
        {dropDownArrowComponent || <ExpandMoreIcon style={{ fontSize: '15px', ...disable ? {color: 'transparent' } : {} }} className={dropDownArrowClassName} />}
      </button>
    </Tooltip>
  );
};

export default SelectButton;
